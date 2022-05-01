import rules

inp=input("Enter the input .bram file name: ")
try:
    file=open(inp+'.bram','r').read()
    out=open(inp+'_output.slt','w')
    try:
        proof=[i.strip() for i in file.split('\n')[8:-1]]
        all_proof=rules.org(proof,['</proof>']) # temp store all proof
        all_step=[] # store all steps by order 
        proof_order={} # store all proof in order
        steps={} # store all steps as steps={step id:[expression,rules,premise,coordinate]}
        
        # find the id of each step
        for i in all_proof:
            i[0]=rules.find(i[0])
        
        # create a dictionary with each subproof id as the key and each step id in the subproof as value
        for k in all_proof:
            a=[]
            for m in k[1:]:
                if m[0:20]=='<assumption linenum=' or m[0:14]=='<step linenum=':
                    a.append(rules.find(m))
            proof_order[k[0]]=a
        
        # put the steps in to a list
        for i in all_proof:
            all_step+=rules.org(i[1:-1],['</assumption>','</step>'])
        for i in all_step:
            i[0]=rules.find(i[0])
        
        # remove any duplicate in the steps
        all_step=sorted(all_step)
        for i in range(0,len(all_step)-1):
            if all_step[i][0]==all_step[i+1][0]:
                all_step[i]+=all_step[i+1][1:]
                all_step[i+1]=all_step[i]
        all_step=rules.remove(all_step)
        
        # put the final steps in to the dictionary
        for i in all_step:
            # remove all the other parts, leave only the expression 
            for j in range(1,len(i)-1):
                i[j]=rules.exp(i[j])
            # replace the rules in to .slt form 
            for k in range(1,len(i)):
                i[k]=rules.check(i[k])
            # put the final proof in to dictionary, step id as the key and a list like
            # [expression,rule,premise] as the value
            steps[i[0]]=rules.change(i)
        arr=len(steps)-1
        
        # change the structure, from the first line of subproof to the last line
        for m in steps.keys():
            if len(proof_order.keys())>1 and steps[m][2]!='NIL':
                for k in range(0,len(steps[m][2])):
                    for z in proof_order.keys():
                        if (int(steps[m][2][k]) in proof_order[z]) and (z!=0) and (m>proof_order[z][-1]):
                            steps[m][2].pop(k)
                            steps[m][2].insert(k,str(proof_order[z][-1]))
        
        # fix the conditional and biconditional introduction rule in .slt 
        rules.if_iff(steps,proof_order)
        
        # fix the both contradiction rule in .slt 
        rules.con(steps)
        
        # fix the double negation and the reiteration rule in .slt
        rules.DE_RET(steps)
        
        # delete the contradiction rules
        rules.delete(steps)
        
        # set the coordinate of each expression in .slt
        arrange={arr:0}
        rules.location([arr],arrange,steps,0)
        rules.coordinate(arrange,steps)
        
        for m in steps.keys():
            # change all the symbol from .bram to .slt symbol
            steps[m][0]=rules.slate_sym(steps[m][0])
            
            # change all the steps from .bram to .slt steps
            steps[m].append(rules.slate(steps[m],m))
            #print(m,steps[m])
        
        # put everything together in the .slt file 
        out.write(rules.start)
        for m in steps.keys():
            # write in each step, avoid contradiction rule
            out.write(steps[m][-1])
        structure=rules.st(steps)
        out.write(structure)
        out.write(rules.end)
        out.close()
        print("The output is in '{}_output.slt' file".format(inp))
    except:
        print("TypeError\nWrong type input file")
except:
    print("FileNotFoundError\nNo such file or directory")