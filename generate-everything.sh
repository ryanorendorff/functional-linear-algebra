find src/ -type f -name "*.agda" | xargs -0 | sed 's/src\///g; s/\.agda//g; s/\//./g; /^$/d' | awk '{print "import " $0}' > Everything.agda
