#/usr/bin/python
import subprocess
import sys

lines = []
started = false

for line in sys.stdin:
        if (started):

        else:
                if line = "%%%%%%%%\n":
                        p = subprocess.Popen(args, stdin=subprocess.PIPE, stdout=sys.stdout, creationflags=subprocess.CREATE_NEW_PROCESS_GROUP)
                        p.stdin.writelines(lines)
                        p.stdin.close()



