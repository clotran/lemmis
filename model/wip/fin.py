import re,sys
src,dst,comment=sys.argv[1],sys.argv[2],sys.argv[3]
incs=sys.argv[4:]
t=open(src).read()
X=r'([^\s()]+|\((?:[^()]|\([^()]*\))*\))'
t=re.sub(r'\(no-calls (:term|:list) '+X+r' sigs nil\)', r'(sfc-ok \1 \2 sigs st)', t)
# bare no-calls in theory lists: disable sfc-ok as well
t=re.sub(r'(?<=[\s(])no-calls(?=[\s)])', 'no-calls sfc-ok', t)
t=t.replace('(no-calls sfc-ok :', '(no-calls :')
lines=t.split('\n',2)
body=lines[2]
hdr=comment+'\n\n(in-package "ACL2")\n\n'+''.join('(include-book "%s")\n'%i for i in incs)
open(dst,'w').write(hdr+body)
