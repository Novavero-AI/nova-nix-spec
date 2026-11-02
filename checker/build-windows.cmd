@echo off
rem Builds mmcheck.exe with the tools a stage0-pe32 checkout built from its
rem seed by x86\mescc-tools-mini.cmd. Nothing else compiles any part of it.
rem
rem Usage: build-windows.cmd STAGE0_PE32_DIR OUTPUT_DIR

if "%~2"=="" (
	echo usage: build-windows.cmd STAGE0_PE32_DIR OUTPUT_DIR
	exit /b 2
)

setlocal
set HERE=%~dp0
set STAGE0=%~f1
set OUT=%~f2
set ART=%STAGE0%\x86\artifact
set X86=%STAGE0%\x86
set LIBC=%STAGE0%\M2libc
if not exist "%OUT%" mkdir "%OUT%"

"%ART%\M2.exe" --architecture x86 ^
	-D __windows__=1 ^
	-f "%LIBC%\sys\types.h" ^
	-f "%LIBC%\stddef.h" ^
	-f "%LIBC%\sys\utsname.h" ^
	-f "%LIBC%\x86\windows\ntdll.c" ^
	-f "%LIBC%\x86\windows\unistd.c" ^
	-f "%LIBC%\x86\windows\process.c" ^
	-f "%LIBC%\x86\windows\fcntl.c" ^
	-f "%LIBC%\fcntl.c" ^
	-f "%LIBC%\x86\windows\sys\stat.c" ^
	-f "%LIBC%\ctype.c" ^
	-f "%LIBC%\stdlib.c" ^
	-f "%LIBC%\stdarg.h" ^
	-f "%LIBC%\stdio.h" ^
	-f "%LIBC%\stdio.c" ^
	-f "%LIBC%\bootstrappable.c" ^
	-f "%HERE%mmcheck.c" ^
	-o "%OUT%\mmcheck.M1" || goto :fail
"%ART%\catm.exe" "%OUT%\mmcheck-0.M1" "%LIBC%\x86\x86_defs.M1" "%X86%\libc-core.M1" "%X86%\libc-full.M1" "%OUT%\mmcheck.M1" "%X86%\pe-end-shim.M1" || goto :fail
"%ART%\M0.exe" "%OUT%\mmcheck-0.M1" "%OUT%\mmcheck.hex2" || goto :fail
"%ART%\catm.exe" "%OUT%\mmcheck-0.hex2" "%X86%\PE32-i386.hex2" "%X86%\ntdll-i386.hex2" "%OUT%\mmcheck.hex2" || goto :fail
"%ART%\hex2.exe" "%OUT%\mmcheck-0.hex2" "%OUT%\mmcheck.exe" || goto :fail
exit /b 0

:fail
echo BUILD FAILED
exit /b 1
