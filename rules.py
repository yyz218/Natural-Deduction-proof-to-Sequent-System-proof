def Natural_Deduction_rules():
    ND_rules={'ADDITION':'OR-INTRO','CONJUNCTION':'AND-INTRO','CONDITIONAL_PROOF':'IF-INTRO',
 'PROOF_BY_CONTRADICTION':'NOT-INTRO','CONTRADICTION':'Con-I','BICONDITIONAL_INTRO':'IFF-INTRO',
 'DISJUNCTIVE_ELIMINATION':'OR-ELIM','SIMPLIFICATION':'AND-ELIM','MODUS_PONENS':'IF-ELIM',
 'DOUBLENEGATION':'DE','PRINCIPLE_OF_EXPLOSION':'Con-E','BICONDITIONAL_ELIM':'IFF-ELIM'
 ,'REITERATION':'RET'}
    return ND_rules

def symbols():
    symbols={'âˆ¨':'|','âˆ§':'&','Â¬':'~','â†’':'$','â†”':'%','âŠ¥':'^'}
    return symbols

def slate_symbols():
    symbols={'~':'not','$':'if','%':'iff','|':'or','&':'and','^':'con'}
    return symbols

# find the id in the line
def find(s):
    a=''
    for i in s:
        if i.isdigit():
            a+=i
    return int(a)

# organize the input
def org(s,l):
    final=[]
    a=[]
    for k in s:
        a.append(k)
        if k in l:
            final.append(a)
            a=[]
    return final

# remove the unnecessary part of the input line
def exp(a):
    if '<raw>' in a and '</raw>' in a:
        return ''.join(''.join(a.split('</raw>')).split('<raw>'))
    elif '<rule>' in a and '</rule>' in a:
        return ''.join(''.join(a.split('<rule>')).split('</rule>'))
    elif '<premise>' in a and '</premise>' in a:
        return ''.join(''.join(a.split('<premise>')).split('</premise>'))
    elif a in ['</assumption>','</step>']:
        return a
        
# remove duplicate of the input
def remove(a):
    b=[]
    for k in range(0,len(a)-1):
        if a[k]!=a[k+1]:
            b.append(a[k])
    b.append(a[-1])
    return b

# replace the symbol and rules to .slt form 
def check(a):
    s=symbols()
    r=Natural_Deduction_rules()
    for m in s.keys():
        while m in a:
            a=a.replace(m,s[m])
    for m in r.keys():
        while m in a:
            a=a.replace(m,r[m])
    return a

# change the step to a list
def change(a):
    if '</assumption>' in a and '</step>' not in a:
        return [a[1],'ASSUME','NIL']
    elif '</step>' in a and '</assumption>' not in a:
        f=[a[1],a[2],a[3:-1]]
        return f
    elif '</step>' in a and '</assumption>' in a:
        f=[a[1],'ASSUME','NIL']
        return f

# change the symbol to word that can be use in .slt file
def slate_sym(a):
    s=slate_symbols()
    for m in s.keys():
        while m in a:
            z=a.find(m)
            if m=='~':
                if a[z+1]=='~':
                    z=z+1
                if a[z+1]=='(':
                    k=0
                    for n in range(z+2,len(a)):
                        if a[n]=='(':
                            k+=1
                        elif a[n]==')':
                            k-=1
                        if k==-1:
                            k=n
                            break
                    a=a[:z]+'(not '+a[z+1:k+1]+')'+a[k+1:]
                else:
                    if ' ' in a[z:]:
                        a=a[:z]+'(not '+a[z+1:a[z:].find(' ')+z]+')'+a[a[z:].find(' ')+z:]
                    else:
                        a=a[:z]+'(not '+a[z+1:]+')'
            elif m=='^':
                a=a.replace(m,s[m])
            else:
                left=0
                a=a[:z]+a[z+1:]
                for n in range(z,-1,-1):
                    if a[n]=='(':
                        left-=1
                    elif a[n]==')':
                        left+=1
                    if left==-1:
                        left=n
                        break
                if s[m]!=a[left+1:left+4] and s[m]!=a[left+1:left+3]:
                    a=a[:left+1]+s[m]+' '+a[left+1:]    
    return a

# change each step to .slt form
def slate(a,i):
    b="""
   (:X
   {}
   :Y
   {}
   :ID
   {}
   :NAME
   ""
   :FORMULA
   "{}"
   :JUSTIFICATION
   LOGIC::{})""".format(a[3][0],a[3][1],str(i),a[0],a[1])
    return b

# construct the structures of the .slt file
def st(a):
    b=""")
 :STRUCTURES
 ("""
    for m in a.keys():
        if a[m][2]=='NIL':
            b=b+'\n'+'(:CONCLUSION {} :PREMISES {})'.format(m,'NIL')
        elif a[m][1]=='Con-I':
            continue
        else:
            b=b+'\n'+'(:CONCLUSION {} :PREMISES ({}))'.format(m,' '.join(a[m][2]))            
    return b

# contradictin elimination rule in nutraul deduction to .slt rule
def elim(e,p1,p2,inp,outp):
    a=len(inp)+len(outp)
    if inp[e][0][0]=='~':
        outp[a]=[inp[e][0][1:], 'ASSUME', 'NIL']
    else:
        outp[a]=['~'+inp[e][0], 'ASSUME', 'NIL']
    outp[a+1]=['( '+outp[a][0]+' & '+inp[int(p1)][0]+' & '+inp[int(p2)][0]+' )', 'AND-INTRO', [p1,p2,str(a)]]
    outp[a+2]=[inp[int(p1)][0],'AND-ELIM',[str(a+1)]]
    outp[a+3]=[inp[int(p2)][0],'AND-ELIM',[str(a+1)]]
    outp[e]=inp[e]
    outp[e][2]=[str(a+2),str(a+3)]
    return outp

# check if the expression starts with not
def no(a):
    if a[0][0]=='~':
        a[1]='NOT-INTRO'
    else:
        a[1]='NOT-ELIM'

# conditional and biconditional introduction rule in nutraul deduction to .slt rule
def if_iff(steps,proof_order):
    outp={}
    for m in steps.keys():
        if steps[m][1]=='IF-INTRO' or steps[m][1]=='IFF-INTRO':
            p1=int(steps[m][2][0])
            t=True
            for d in sorted(proof_order.keys()):
                if p1 in proof_order[d]:
                    p2=str(proof_order[d][0])
            for f in range(int(p2)+1,p1+1):
                if p2 in steps[f][2]:
                    t=False
                    break
            if t:
                a=len(steps)+len(outp)
                outp[a]=steps[p1]
                outp[a+1]=['(and '+steps[p1][0]+' '+steps[int(p2)][0]+')','AND-INTRO', [str(a),p2]]
                outp[p1]=[steps[p1][0],'AND-ELIM',[str(a+1)]]
            if steps[m][1]=='IFF-INTRO':
                p1=int(steps[m][2][1])
                t=True
                for d in sorted(proof_order.keys()):
                    if p1 in proof_order[d]:
                        p2=str(proof_order[d][0])
                for f in range(int(p2)+1,p1+1):
                    if p2 in steps[f][2]:
                        t=False
                        break
                if t:
                    a=len(steps)+len(outp)
                    outp[a]=steps[p1]
                    outp[a+1]=['(and '+steps[p1][0]+' '+steps[int(p2)][0]+')','AND-INTRO', [str(a),p2]]
                    outp[p1]=[steps[p1][0],'AND-ELIM',[str(a+1)]]

    # put extra steps needed to all the steps    
    for m in outp.keys():
        steps[m]=outp[m]

# double negation and reiteration rule in nutraul deduction to .slt rule
def DE_RET(steps):
    extra={}
    for m in steps.keys():
        if steps[m][1]=='DE':
            a=len(steps)+len(extra)
            extra[a]=['~'+steps[m][0],'ASSUME', 'NIL']
            steps[m][2].append(str(a))
            steps[m][1]='NOT-ELIM'
        elif steps[m][1]=='RET':
            a=len(steps)+len(extra)
            if steps[m][0][0]=='~':
                extra[a]=[steps[m][0][1:],'ASSUME', 'NIL']
            else:
                extra[a]=['~'+steps[m][0],'ASSUME', 'NIL']
            no(steps[m])
            steps[m][2].append(str(a))

    # put extra steps needed to all the steps    
    for m in extra.keys():
        steps[m]=extra[m]

# both contradiction rule in nutraul deduction to .slt rule
def con(steps):
    extra={}
    for m in steps.keys():
        # fix the contradiction introduction rule in .slt 
        if steps[m][1]=='NOT-INTRO':
            steps[m][2]=steps[int(steps[m][2][0])][2]
            
        # fix the contradiction elimination rule in .slt 
        elif steps[m][1]=='Con-E':
            steps[m][2]=steps[int(steps[m][2][0])][2]
            no(steps[m])
            extra=elim(m,steps[m][2][0],steps[m][2][1],steps,extra)
            
    # put extra steps needed to all the steps    
    for m in extra.keys():
        steps[m]=extra[m]

def location(m,arrange,steps,zero):
    l=[int(k) for z in m for k in steps[z][2] if steps[z][2]!='NIL']
    if len(l)!=0:
        for o in l:
            arrange[o]=zero+1
        location(l,arrange,steps,zero+1)

def coordinate(arrange,steps):
    coordinate={}
    for t in arrange.values():
        if t not in coordinate.keys():
            coordinate[t]=[0]
        else:
            coordinate[t].append(0)

    for u in coordinate:
        for z in range(len(coordinate[u])):
            tmp=int((1230-165*len(coordinate[u]))/(len(coordinate[u])+1))
            x=120+tmp+(165+tmp)*z
            y=(max(arrange.values())-u)*115+50
            coordinate[u][z]=[x,y]
        #print(u,coordinate[u])
        
    for m in arrange.keys():
        tmp=arrange[m]
        arrange[m]=coordinate[tmp][0]
        coordinate[tmp]=coordinate[tmp][1:]
        steps[m].append(arrange[m])
    

def delete(steps):
    c=[]
    for u in steps.keys():
        if steps[u][0]=='^':
            c.append(u)
    for l in c:
        del steps[l]

start="""(:DESCRIPTIONS
 ("""
  
end=""")
 :INTERFACE
 (:X
  -10
  :Y
  0
  :WIDTH
  1540
  :HEIGHT
  1000
  :PROOF-SYSTEM
  LOGIC::PROPOSITIONAL-CALCULUS))"""