"""Lanza una orden con doble fork y setsid, bajo caffeinate -is, para que no dependa de la app."""
import os, sys
orden, log = sys.argv[1], sys.argv[2]
if os.fork():
    os._exit(0)
os.setsid()
if os.fork():
    os._exit(0)
fd = os.open(log, os.O_WRONLY | os.O_CREAT | os.O_APPEND, 0o644)
os.dup2(fd, 1); os.dup2(fd, 2)
os.close(0)
os.execvp("caffeinate", ["caffeinate", "-is", "/bin/zsh", orden])
