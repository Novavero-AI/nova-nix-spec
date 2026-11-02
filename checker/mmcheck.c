/* mmcheck: a Metamath proof checker in the C subset M2-Planet compiles.
 *
 * Usage: mmcheck database.mm
 *
 * Exit status 0 means every statement parsed and every $p proof checked.
 * Anything else is a refusal. A proof containing the unknown step `?` is
 * refused: the language lets a verifier skip one, and a skipped theorem
 * would still be usable by everything after it.
 *
 * The rules are section 4.1 and appendix on compressed proofs of the Metamath
 * book. The logic is not here: axioms live in the database as $a statements,
 * so one checker serves any logic, and accepting a database means only that
 * its $p statements follow from its $a statements.
 *
 * Going past a capacity below refuses the database, so a limit can cost
 * completeness and never soundness. Every expression lives in one of two int
 * arrays and is named by offset and length: int is 4 bytes on x86 and 8 on
 * amd64 under M2-Planet, and offsets keep every access checkable in one place.
 *
 * Upstream M2-Planet compiles && and || as & and |, evaluating both sides. So
 * both sides here are always 0 or 1 and always safe to evaluate, which gives
 * this file one meaning under that compiler, under the fixed one, and under C.
 */

#include <stdio.h>
#include <stdlib.h>

#define MAX_SYMS 262144
#define HASH_SIZE 1048576 /* A power of two, at least twice MAX_SYMS */
#define MAX_FILES 64
#define MAX_DEPTH 256
#define MAX_ACTIVE 16384
#define MAX_DV 262144
#define MAX_EXPR 262144
#define PERM_WORDS 8388608
#define PROOF_WORDS 4194304
#define MAX_STACK 65536
#define MAX_TAGS 65536
#define MAX_LABELS 65536
#define MAX_STEP 16777216 /* Small enough that 20 * MAX_STEP fits 31 bits */
#define FILE_CHUNK 1048576

/* What a token has been declared as. */
#define K_NONE 0
#define K_CONST 1
#define K_VAR 2
#define K_FLOAT 3
#define K_ESSENTIAL 4
#define K_AXIOM 5
#define K_THEOREM 6

int sym_count;
char** sym_name;
int* sym_kind;
int* sym_active; /* A variable or hypothesis currently in scope */
int* sym_float; /* A variable's active $f label, or 0 */
int* sym_type; /* A variable's typecode, fixed by its first $f */
int* expr_off; /* A statement's expression in perm */
int* expr_len;
int* hyps_off; /* An assertion's mandatory hypotheses in perm */
int* hyps_len;
int* dvs_off; /* An assertion's mandatory $d pairs in perm */
int* dvs_len;
int* mark; /* Stamped to mark a symbol as mandatory */
int mark_stamp;
int* sub_off; /* A variable's substitution in proof */
int* sub_len;
int* sub_set; /* Stamped when a variable's substitution is set */
int sub_stamp;
int* hash_tab;

int* perm;
int perm_top;
int* proof;
int proof_top;

int* active_hyps;
int active_hyp_top;
int* active_vars;
int active_var_top;
int* dv; /* Pairs (a, b) with a < b */
int dv_top;
int depth;
int* saved_hyps;
int* saved_vars;
int* saved_dv;

int* expr_buf;
int expr_buf_len;

int* st_off;
int* st_len;
int sp;
int* tag_off;
int* tag_len;
int tag_count;
int* labels;
int label_count;

char** file_buf;
int* file_pos;
int* file_len;
char** file_names;
int file_name_count;
int file_top;
char* cur_buf;
int cur_pos;
int cur_len;

int axiom_count;
int theorem_count;

void die(char* why, char* what)
{
	fputs("refused: ", stderr);
	fputs(why, stderr);
	if(NULL != what)
	{
		fputs(": ", stderr);
		fputs(what, stderr);
	}
	fputs("\n", stderr);
	fflush(stderr);
	exit(1);
}

int* new_ints(int n)
{
	int* p = calloc(n, sizeof(int));
	if(NULL == p) die("out of memory", NULL);
	return p;
}

void put_int(int n)
{
	char digits[32];
	int i = 0;
	if(0 == n) fputs("0", stdout);
	while(0 < n)
	{
		digits[i] = '0' + (n % 10);
		n = n / 10;
		i = i + 1;
	}
	char one[2];
	one[1] = 0;
	while(0 < i)
	{
		i = i - 1;
		one[0] = digits[i];
		fputs(one, stdout);
	}
}

int streq(char* a, char* b)
{
	int i = 0;
	while(a[i] == b[i])
	{
		if(0 == a[i]) return 1;
		i = i + 1;
	}
	return 0;
}

int is_space(int c)
{
	if(32 == c) return 1;
	if(9 == c) return 1;
	if(10 == c) return 1;
	if(12 == c) return 1;
	if(13 == c) return 1;
	return 0;
}

/* ---- Symbols ---- */

int intern(char* name)
{
	unsigned h = 5381;
	int i = 0;
	while(0 != name[i])
	{
		h = (h * 33) + (name[i] & 255);
		i = i + 1;
	}
	unsigned slot = h & (HASH_SIZE - 1);
	while(0 != hash_tab[slot])
	{
		if(streq(sym_name[hash_tab[slot]], name)) return hash_tab[slot];
		slot = (slot + 1) & (HASH_SIZE - 1);
	}
	if(sym_count >= MAX_SYMS - 1) die("too many symbols", name);
	sym_count = sym_count + 1;
	sym_name[sym_count] = name;
	hash_tab[slot] = sym_count;
	return sym_count;
}

int perm_alloc(int n)
{
	if(n > PERM_WORDS - perm_top) die("permanent storage exhausted", NULL);
	int off = perm_top;
	perm_top = perm_top + n;
	return off;
}

/* ---- Files and tokens ---- */

void load_file(char* name)
{
	if(file_top >= MAX_FILES) die("files nested too deeply", name);
	FILE* f = fopen(name, "r");
	if(NULL == f) die("cannot read file", name);

	int cap = FILE_CHUNK;
	int n = 0;
	char* b = malloc(cap);
	if(NULL == b) die("out of memory", name);
	int c = fgetc(f);
	while(EOF != c)
	{
		if(!is_space(c))
		{
			if(33 > c) die("character not allowed in file", name);
			if(126 < c) die("character not allowed in file", name);
		}
		if(n + 1 >= cap)
		{
			if(cap > 536870912) die("file too large", name);
			char* bigger = malloc(cap * 2);
			if(NULL == bigger) die("out of memory", name);
			int i;
			for(i = 0; i < n; i = i + 1) bigger[i] = b[i];
			free(b);
			b = bigger;
			cap = cap * 2;
		}
		b[n] = c;
		n = n + 1;
		c = fgetc(f);
	}
	fclose(f);
	b[n] = 0;

	if(0 < file_top)
	{
		file_pos[file_top - 1] = cur_pos;
	}
	file_buf[file_top] = b;
	file_pos[file_top] = 0;
	file_len[file_top] = n;
	file_top = file_top + 1;
	cur_buf = b;
	cur_pos = 0;
	cur_len = n;
}

/* Returns 0 once the top-level file is finished. */
int pop_file(void)
{
	if(0 != depth) die("block left open at end of file", NULL);
	file_top = file_top - 1;
	if(0 == file_top) return 0;
	cur_buf = file_buf[file_top - 1];
	cur_pos = file_pos[file_top - 1];
	cur_len = file_len[file_top - 1];
	return 1;
}

/* Tokens end up NUL terminated in place, and symbols keep pointing at them. */
char* raw_token(void)
{
	while(cur_pos < cur_len && is_space(cur_buf[cur_pos])) cur_pos = cur_pos + 1;
	if(cur_pos >= cur_len) return NULL;
	int start = cur_pos;
	while(cur_pos < cur_len && !is_space(cur_buf[cur_pos])) cur_pos = cur_pos + 1;
	cur_buf[cur_pos] = 0;
	if(cur_pos < cur_len) cur_pos = cur_pos + 1;
	/* Not &cur_buf[start]: in &p[i] on a pointer, M2-Planet starts from the
	 * address of p and not from its value, both at the stage0-pe32 pin and at
	 * upstream ebfecc2. This can change once a pinned compiler gets it right. */
	return cur_buf + start;
}

int has_dollar(char* t)
{
	int i = 0;
	while(0 != t[i])
	{
		if('$' == t[i]) return 1;
		i = i + 1;
	}
	return 0;
}

int has_comment_marker(char* t)
{
	int i = 0;
	while(0 != t[i])
	{
		if('$' == t[i])
		{
			if('(' == t[i + 1]) return 1;
			if(')' == t[i + 1]) return 1;
		}
		i = i + 1;
	}
	return 0;
}

/* Skips a comment whose opening marker has been read. */
void skip_comment(void)
{
	while(1)
	{
		char* t = raw_token();
		if(NULL == t) die("comment not closed", NULL);
		if(streq(t, "$)")) return;
		if(has_comment_marker(t)) die("comment marker inside a comment", t);
	}
}

/* The next token that is not inside a comment, or NULL at end of file. */
char* next_token(void)
{
	char* t = raw_token();
	while(1)
	{
		if(NULL == t) return NULL;
		if(!streq(t, "$(")) return t;
		skip_comment();
		t = raw_token();
	}
}

char* need_token(void)
{
	char* t = next_token();
	if(NULL == t) die("file ends inside a statement", NULL);
	return t;
}

void check_label_token(char* t)
{
	int i = 0;
	while(0 != t[i])
	{
		int c = t[i];
		int ok = 0;
		if('a' <= c && c <= 'z') ok = 1;
		if('A' <= c && c <= 'Z') ok = 1;
		if('0' <= c && c <= '9') ok = 1;
		if('-' == c || '_' == c || '.' == c) ok = 1;
		if(!ok) die("character not allowed in label", t);
		i = i + 1;
	}
}

/* ---- Blocks ---- */

void open_block(void)
{
	if(depth >= MAX_DEPTH) die("blocks nested too deeply", NULL);
	saved_hyps[depth] = active_hyp_top;
	saved_vars[depth] = active_var_top;
	saved_dv[depth] = dv_top;
	depth = depth + 1;
}

void close_block(void)
{
	if(0 == depth) die("$} without a matching ${", NULL);
	depth = depth - 1;
	while(active_hyp_top > saved_hyps[depth])
	{
		active_hyp_top = active_hyp_top - 1;
		int h = active_hyps[active_hyp_top];
		sym_active[h] = 0;
		if(K_FLOAT == sym_kind[h]) sym_float[perm[expr_off[h] + 1]] = 0;
	}
	while(active_var_top > saved_vars[depth])
	{
		active_var_top = active_var_top - 1;
		sym_active[active_vars[active_var_top]] = 0;
	}
	dv_top = saved_dv[depth];
}

/* ---- Declarations ---- */

void declare_constants(void)
{
	if(0 != depth) die("$c outside the outermost block", NULL);
	int n = 0;
	char* t = need_token();
	while(!streq(t, "$."))
	{
		if(has_dollar(t)) die("$ in a math symbol", t);
		int s = intern(t);
		if(K_NONE != sym_kind[s]) die("constant declared over an existing name", t);
		sym_kind[s] = K_CONST;
		n = n + 1;
		t = need_token();
	}
	if(0 == n) die("empty $c statement", NULL);
}

void declare_variables(void)
{
	int n = 0;
	char* t = need_token();
	while(!streq(t, "$."))
	{
		if(has_dollar(t)) die("$ in a math symbol", t);
		int s = intern(t);
		if(K_NONE == sym_kind[s]) sym_kind[s] = K_VAR;
		else if(K_VAR != sym_kind[s]) die("variable declared over an existing name", t);
		else if(sym_active[s]) die("variable declared while active", t);
		if(active_var_top >= MAX_ACTIVE) die("too many active variables", t);
		sym_active[s] = 1;
		active_vars[active_var_top] = s;
		active_var_top = active_var_top + 1;
		n = n + 1;
		t = need_token();
	}
	if(0 == n) die("empty $v statement", NULL);
}

void declare_disjoint(void)
{
	int n = 0;
	char* t = need_token();
	while(!streq(t, "$."))
	{
		int s = intern(t);
		if(K_VAR != sym_kind[s]) die("$d on something not a variable", t);
		if(!sym_active[s]) die("$d on an inactive variable", t);
		if(n >= MAX_EXPR) die("$d too long", t);
		int i;
		for(i = 0; i < n; i = i + 1)
		{
			if(expr_buf[i] == s) die("variable repeated in $d", t);
			if(dv_top + 2 > MAX_DV) die("too many active $d pairs", t);
			if(expr_buf[i] < s)
			{
				dv[dv_top] = expr_buf[i];
				dv[dv_top + 1] = s;
			}
			else
			{
				dv[dv_top] = s;
				dv[dv_top + 1] = expr_buf[i];
			}
			dv_top = dv_top + 2;
		}
		expr_buf[n] = s;
		n = n + 1;
		t = need_token();
	}
	if(2 > n) die("$d needs two variables", NULL);
}

/* ---- Expressions ---- */

/* Reads a typecode and active symbols up to `stop` into expr_buf. */
void read_expr(char* stop)
{
	expr_buf_len = 0;
	char* t = need_token();
	if(streq(t, stop)) die("statement has no typecode", NULL);
	if(K_CONST != sym_kind[intern(t)]) die("typecode is not a constant", t);
	while(!streq(t, stop))
	{
		int s = intern(t);
		if(K_VAR == sym_kind[s])
		{
			if(!sym_active[s]) die("inactive variable", t);
			if(0 == sym_float[s]) die("variable has no active $f", t);
		}
		else if(K_CONST != sym_kind[s]) die("not an active math symbol", t);
		if(expr_buf_len >= MAX_EXPR) die("expression too long", t);
		expr_buf[expr_buf_len] = s;
		expr_buf_len = expr_buf_len + 1;
		t = need_token();
	}
}

void store_expr(int id)
{
	int off = perm_alloc(expr_buf_len);
	int i;
	for(i = 0; i < expr_buf_len; i = i + 1) perm[off + i] = expr_buf[i];
	expr_off[id] = off;
	expr_len[id] = expr_buf_len;
}

void push_active_hyp(int id)
{
	if(active_hyp_top >= MAX_ACTIVE) die("too many active hypotheses", sym_name[id]);
	active_hyps[active_hyp_top] = id;
	active_hyp_top = active_hyp_top + 1;
	sym_active[id] = 1;
}

void declare_float(int id)
{
	char* t = need_token();
	int type = intern(t);
	if(K_CONST != sym_kind[type]) die("$f typecode is not a constant", t);
	t = need_token();
	int v = intern(t);
	if(K_VAR != sym_kind[v]) die("$f on something not a variable", t);
	if(!sym_active[v]) die("$f on an inactive variable", t);
	if(0 != sym_float[v]) die("variable already has an active $f", t);
	if(0 != sym_type[v] && sym_type[v] != type) die("variable given a second type", t);
	if(!streq(need_token(), "$.")) die("$f statement too long", sym_name[id]);

	sym_type[v] = type;
	expr_buf[0] = type;
	expr_buf[1] = v;
	expr_buf_len = 2;
	store_expr(id);
	sym_kind[id] = K_FLOAT;
	sym_float[v] = id;
	push_active_hyp(id);
}

void declare_essential(int id)
{
	read_expr("$.");
	store_expr(id);
	sym_kind[id] = K_ESSENTIAL;
	push_active_hyp(id);
}

/* Records what using this assertion requires: its mandatory hypotheses in
 * database order, and the $d pairs whose variables are both mandatory. The
 * expression has been stored. */
void make_frame(int id)
{
	int i;
	int j;
	mark_stamp = mark_stamp + 1;
	for(i = 0; i < expr_len[id]; i = i + 1)
	{
		int s = perm[expr_off[id] + i];
		if(K_VAR == sym_kind[s]) mark[s] = mark_stamp;
	}
	for(i = 0; i < active_hyp_top; i = i + 1)
	{
		int h = active_hyps[i];
		if(K_ESSENTIAL == sym_kind[h])
		{
			for(j = 0; j < expr_len[h]; j = j + 1)
			{
				int s = perm[expr_off[h] + j];
				if(K_VAR == sym_kind[s]) mark[s] = mark_stamp;
			}
		}
	}

	int n = 0;
	for(i = 0; i < active_hyp_top; i = i + 1)
	{
		int h = active_hyps[i];
		if(K_ESSENTIAL == sym_kind[h]) n = n + 1;
		else if(mark[perm[expr_off[h] + 1]] == mark_stamp) n = n + 1;
	}
	int off = perm_alloc(n);
	n = 0;
	for(i = 0; i < active_hyp_top; i = i + 1)
	{
		int h = active_hyps[i];
		int mandatory = 0;
		if(K_ESSENTIAL == sym_kind[h]) mandatory = 1;
		else if(mark[perm[expr_off[h] + 1]] == mark_stamp) mandatory = 1;
		if(mandatory)
		{
			perm[off + n] = h;
			n = n + 1;
		}
	}
	hyps_off[id] = off;
	hyps_len[id] = n;

	n = 0;
	for(i = 0; i < dv_top; i = i + 2)
	{
		if(mark[dv[i]] == mark_stamp && mark[dv[i + 1]] == mark_stamp) n = n + 2;
	}
	off = perm_alloc(n);
	n = 0;
	for(i = 0; i < dv_top; i = i + 2)
	{
		if(mark[dv[i]] == mark_stamp && mark[dv[i + 1]] == mark_stamp)
		{
			perm[off + n] = dv[i];
			perm[off + n + 1] = dv[i + 1];
			n = n + 2;
		}
	}
	dvs_off[id] = off;
	dvs_len[id] = n;
}

/* ---- Proofs ---- */

void proof_room(int n)
{
	if(n > PROOF_WORDS - proof_top) die("proof storage exhausted", NULL);
}

void push_entry(int off, int len)
{
	if(sp >= MAX_STACK) die("proof stack too deep", NULL);
	st_off[sp] = off;
	st_len[sp] = len;
	sp = sp + 1;
}

/* Appends a statement's expression, under the current substitution, to the
 * proof array. Returns where it starts; its length is proof_top minus that. */
int substitute(int off, int len)
{
	int start = proof_top;
	int i;
	for(i = 0; i < len; i = i + 1)
	{
		int s = perm[off + i];
		if(K_VAR == sym_kind[s])
		{
			if(sub_set[s] != sub_stamp) die("variable with no substitution", sym_name[s]);
			int n = sub_len[s];
			proof_room(n);
			int j;
			for(j = 0; j < n; j = j + 1) proof[proof_top + j] = proof[sub_off[s] + j];
			proof_top = proof_top + n;
		}
		else
		{
			proof_room(1);
			proof[proof_top] = s;
			proof_top = proof_top + 1;
		}
	}
	return start;
}

int disjoint_declared(int a, int b)
{
	int low = a;
	int high = b;
	if(a > b)
	{
		low = b;
		high = a;
	}
	int i;
	for(i = 0; i < dv_top; i = i + 2)
	{
		if(dv[i] == low && dv[i + 1] == high) return 1;
	}
	return 0;
}

void check_disjoint(int a)
{
	int i;
	for(i = 0; i < dvs_len[a]; i = i + 2)
	{
		int x = perm[dvs_off[a] + i];
		int y = perm[dvs_off[a] + i + 1];
		if(sub_set[x] != sub_stamp) die("$d variable with no substitution", sym_name[x]);
		if(sub_set[y] != sub_stamp) die("$d variable with no substitution", sym_name[y]);
		int p;
		for(p = 0; p < sub_len[x]; p = p + 1)
		{
			int v = proof[sub_off[x] + p];
			if(K_VAR == sym_kind[v])
			{
				int q;
				for(q = 0; q < sub_len[y]; q = q + 1)
				{
					int w = proof[sub_off[y] + q];
					if(K_VAR == sym_kind[w])
					{
						if(v == w) die("$d violated: shared variable", sym_name[v]);
						if(!disjoint_declared(v, w)) die("$d violated: no $d in scope", sym_name[a]);
					}
				}
			}
		}
	}
}

void apply_assertion(int a)
{
	int n = hyps_len[a];
	if(sp < n) die("proof stack underflow", sym_name[a]);
	int base = sp - n;
	sub_stamp = sub_stamp + 1;

	int i;
	for(i = 0; i < n; i = i + 1)
	{
		int h = perm[hyps_off[a] + i];
		int entry_off = st_off[base + i];
		int entry_len = st_len[base + i];
		if(K_FLOAT == sym_kind[h])
		{
			if(1 > entry_len) die("empty proof stack entry", sym_name[a]);
			if(proof[entry_off] != perm[expr_off[h]]) die("typecode mismatch", sym_name[a]);
			int v = perm[expr_off[h] + 1];
			sub_off[v] = entry_off + 1;
			sub_len[v] = entry_len - 1;
			sub_set[v] = sub_stamp;
		}
		else
		{
			int mark_top = proof_top;
			int start = substitute(expr_off[h], expr_len[h]);
			if(proof_top - start != entry_len) die("hypothesis mismatch", sym_name[a]);
			int j;
			for(j = 0; j < entry_len; j = j + 1)
			{
				if(proof[start + j] != proof[entry_off + j]) die("hypothesis mismatch", sym_name[a]);
			}
			proof_top = mark_top;
		}
	}

	check_disjoint(a);
	int start = substitute(expr_off[a], expr_len[a]);
	sp = base;
	push_entry(start, proof_top - start);
}

void proof_step(int s, char* name)
{
	int k = sym_kind[s];
	if(K_FLOAT == k || K_ESSENTIAL == k)
	{
		if(!sym_active[s]) die("hypothesis not in scope", name);
		proof_room(expr_len[s]);
		int start = proof_top;
		int i;
		for(i = 0; i < expr_len[s]; i = i + 1) proof[start + i] = perm[expr_off[s] + i];
		proof_top = start + expr_len[s];
		push_entry(start, expr_len[s]);
	}
	else if(K_AXIOM == k || K_THEOREM == k) apply_assertion(s);
	else die("proof step is not an earlier statement", name);
}

void compressed_step(int n, int id)
{
	if(n <= label_count)
	{
		proof_step(labels[n - 1], sym_name[id]);
		return;
	}
	int tag = n - label_count - 1;
	if(tag >= tag_count) die("compressed proof step out of range", sym_name[id]);
	push_entry(tag_off[tag], tag_len[tag]);
}

void read_compressed(int id)
{
	int i;
	label_count = 0;
	tag_count = 0;

	/* Numbers 1 to m are the theorem's own mandatory hypotheses. */
	mark_stamp = mark_stamp + 1;
	for(i = 0; i < hyps_len[id]; i = i + 1)
	{
		if(label_count >= MAX_LABELS) die("too many proof labels", sym_name[id]);
		int h = perm[hyps_off[id] + i];
		labels[label_count] = h;
		label_count = label_count + 1;
		mark[h] = mark_stamp;
	}

	char* t = need_token();
	while(!streq(t, ")"))
	{
		int s = intern(t);
		int k = sym_kind[s];
		if(K_FLOAT == k || K_ESSENTIAL == k)
		{
			if(!sym_active[s]) die("hypothesis not in scope", t);
			if(mark[s] == mark_stamp) die("mandatory hypothesis in proof label list", t);
		}
		else if(K_AXIOM != k && K_THEOREM != k) die("proof label is not an earlier statement", t);
		if(label_count >= MAX_LABELS) die("too many proof labels", t);
		labels[label_count] = s;
		label_count = label_count + 1;
		t = need_token();
	}

	/* n accumulates the base 5 digits U to Y; A to T end a number. */
	int n = 0;
	int can_tag = 0;
	t = need_token();
	while(!streq(t, "$."))
	{
		i = 0;
		while(0 != t[i])
		{
			int c = t[i];
			if('A' <= c && c <= 'T')
			{
				if(n > MAX_STEP) die("compressed proof number too large", sym_name[id]);
				n = (n * 20) + (c - 'A') + 1;
				compressed_step(n, id);
				n = 0;
				can_tag = 1;
			}
			else if('U' <= c && c <= 'Y')
			{
				if(n > MAX_STEP) die("compressed proof number too large", sym_name[id]);
				n = (n * 5) + (c - 'U') + 1;
				can_tag = 0;
			}
			else if('Z' == c)
			{
				if(!can_tag) die("Z not directly after a proof step", sym_name[id]);
				if(0 == sp) die("Z on an empty proof stack", sym_name[id]);
				if(tag_count >= MAX_TAGS) die("too many tagged proof steps", sym_name[id]);
				tag_off[tag_count] = st_off[sp - 1];
				tag_len[tag_count] = st_len[sp - 1];
				tag_count = tag_count + 1;
				can_tag = 0;
			}
			else if('?' == c) die("incomplete proof", sym_name[id]);
			else die("character not allowed in compressed proof", sym_name[id]);
			i = i + 1;
		}
		t = need_token();
	}
	if(0 != n) die("compressed proof ends inside a number", sym_name[id]);
}

void read_proof(int id)
{
	proof_top = 0;
	sp = 0;

	char* t = need_token();
	if(streq(t, "(")) read_compressed(id);
	else
	{
		while(!streq(t, "$."))
		{
			if(streq(t, "?")) die("incomplete proof", sym_name[id]);
			proof_step(intern(t), t);
			t = need_token();
		}
	}

	if(1 != sp) die("proof does not end with one result", sym_name[id]);
	if(st_len[0] != expr_len[id]) die("proof proves something else", sym_name[id]);
	int i;
	for(i = 0; i < expr_len[id]; i = i + 1)
	{
		if(proof[st_off[0] + i] != perm[expr_off[id] + i]) die("proof proves something else", sym_name[id]);
	}
}

void declare_axiom(int id)
{
	read_expr("$.");
	store_expr(id);
	make_frame(id);
	sym_kind[id] = K_AXIOM;
	axiom_count = axiom_count + 1;
}

/* The label's kind stays K_NONE until the proof has checked, which is what
 * stops a proof from citing its own theorem. */
void declare_theorem(int id)
{
	read_expr("$=");
	store_expr(id);
	make_frame(id);
	read_proof(id);
	sym_kind[id] = K_THEOREM;
	theorem_count = theorem_count + 1;
}

void labelled_statement(char* label)
{
	check_label_token(label);
	int id = intern(label);
	if(K_NONE != sym_kind[id]) die("label reused or matches a symbol", label);
	char* t = need_token();
	if(streq(t, "$f")) declare_float(id);
	else if(streq(t, "$e")) declare_essential(id);
	else if(streq(t, "$a")) declare_axiom(id);
	else if(streq(t, "$p")) declare_theorem(id);
	else die("label not followed by $f, $e, $a or $p", label);
}

void include_file(void)
{
	if(0 != depth) die("$[ inside a block", NULL);
	char* name = need_token();
	if(has_dollar(name)) die("$ in an included file name", name);
	if(!streq(need_token(), "$]")) die("$[ not closed by $]", name);
	int i;
	for(i = 0; i < file_name_count; i = i + 1)
	{
		if(streq(file_names[i], name)) return;
	}
	if(file_name_count >= MAX_FILES) die("too many included files", name);
	file_names[file_name_count] = name;
	file_name_count = file_name_count + 1;
	load_file(name);
}

void check_database(void)
{
	while(1)
	{
		char* t = next_token();
		if(NULL == t)
		{
			if(!pop_file()) return;
		}
		else if(streq(t, "${")) open_block();
		else if(streq(t, "$}")) close_block();
		else if(streq(t, "$c")) declare_constants();
		else if(streq(t, "$v")) declare_variables();
		else if(streq(t, "$d")) declare_disjoint();
		else if(streq(t, "$[")) include_file();
		else labelled_statement(t);
	}
}

void allocate(void)
{
	sym_name = calloc(MAX_SYMS, sizeof(char*));
	file_buf = calloc(MAX_FILES, sizeof(char*));
	file_names = calloc(MAX_FILES, sizeof(char*));
	if(NULL == sym_name) die("out of memory", NULL);
	if(NULL == file_buf) die("out of memory", NULL);
	if(NULL == file_names) die("out of memory", NULL);
	sym_kind = new_ints(MAX_SYMS);
	sym_active = new_ints(MAX_SYMS);
	sym_float = new_ints(MAX_SYMS);
	sym_type = new_ints(MAX_SYMS);
	expr_off = new_ints(MAX_SYMS);
	expr_len = new_ints(MAX_SYMS);
	hyps_off = new_ints(MAX_SYMS);
	hyps_len = new_ints(MAX_SYMS);
	dvs_off = new_ints(MAX_SYMS);
	dvs_len = new_ints(MAX_SYMS);
	mark = new_ints(MAX_SYMS);
	sub_off = new_ints(MAX_SYMS);
	sub_len = new_ints(MAX_SYMS);
	sub_set = new_ints(MAX_SYMS);
	hash_tab = new_ints(HASH_SIZE);
	perm = new_ints(PERM_WORDS);
	proof = new_ints(PROOF_WORDS);
	active_hyps = new_ints(MAX_ACTIVE);
	active_vars = new_ints(MAX_ACTIVE);
	dv = new_ints(MAX_DV);
	saved_hyps = new_ints(MAX_DEPTH);
	saved_vars = new_ints(MAX_DEPTH);
	saved_dv = new_ints(MAX_DEPTH);
	expr_buf = new_ints(MAX_EXPR);
	st_off = new_ints(MAX_STACK);
	st_len = new_ints(MAX_STACK);
	tag_off = new_ints(MAX_TAGS);
	tag_len = new_ints(MAX_TAGS);
	labels = new_ints(MAX_LABELS);
	file_pos = new_ints(MAX_FILES);
	file_len = new_ints(MAX_FILES);
}

int main(int argc, char** argv)
{
	if(2 != argc)
	{
		fputs("usage: mmcheck database.mm\n", stderr);
		return 2;
	}
	allocate();
	file_names[0] = argv[1];
	file_name_count = 1;
	load_file(argv[1]);
	check_database();

	fputs("ok: ", stdout);
	put_int(theorem_count);
	fputs(" theorems from ", stdout);
	put_int(axiom_count);
	fputs(" axioms\n", stdout);
	fflush(stdout);
	return 0;
}
