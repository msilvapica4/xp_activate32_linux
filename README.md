# xp_activate32_linux

I grew up using MS windows XP, so I'm an enthusiastic for this os.
Recently, I've realized that an executable called xp_activate32.exe had been lauched, and it worked fine on WXP home edition.
later, I've found the suppose source code, but once I'm running Linux on my PC, I needed to make changes to make it works in Linux too.
and was I did. With some modifications in this code, I did this shit work fine on Linux too.
I don't know whether this code will be useful or not, but here you go.
I'm just a beginner programmer, all the merit must be given to the guys who wrote the original code, that I found on 'https://archive.org/details/xp_activate32_src'
This page contains important information: https://github.com/UMSKT/writeups/blob/main/ConfID.md

## Usage

After downloading the file xp_activate32_linux.c, compile it as usual:
```bash
gcc xp_activate32_linux.c -o xp_activate32_linux
```
The sintaxe is:
```bash
$ xp_activate32_linux 'IDENTIFICATION ID'
```
and the program returns the CONFIRMATION ID on the shell window.
