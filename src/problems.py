import cnf


class KnowledgeBase:
    '''
    A KnowledgeBase for Propositional logic.

    '''

    def __init__(self, sentence=None):
        self.clause = []
        if sentence:
            self.tell(sentence)

    def tell(self, sentence):
        '''
        Add the sentence to KnowledgeBase
        also reduce it to smallest structure

        '''
        self.clause.extend(Split('and', cnf.cnf(sentence)))


def combine(op, elements):
    '''
    return the combination of elements using operation op

    '''
    if len(elements) == 0:
        return elements
    elif len(elements) == 1:
        return elements[0]
    elif op == 'and':
        return ['and'] + elements
    elif op == 'or':
        return ['or'] + elements


def Split(op, clause):
    '''
    return the discombination(list) of clause using operation op

    '''
    result = []
    if type(clause) == str:
        return [clause]
    elif len(clause) <= 2:  # P or not P, just return self
        return [clause]
    elif op == clause[0]:
        return clause[1:]
    else:
        return [clause]


def tTEntails(kb, alpha):
    '''
    returns if KB entailments alpha True or False using truth table
    kb: KnowledgeBase
    alpha: the result to prove

    '''
    clause = kb.clause + Split('and', cnf.cnf(alpha))
    symbols = propSymbols(combine('and', clause))

    return tTCheckAll(kb, alpha, symbols, {})


call_times = 0


def tTCheckAll(kb, alpha, symbols, model):
    '''
    help to implement tTEntails
    model is a dictionary such as {'P': True, "Q": False}

    '''

    if len(symbols) == 0:
        alphaCnf = cnf.cnf(alpha)
        # print("kb:", kb.clause)
        # print("model:", model)
        # print("result:", plTrue(alphaCnf, model))
        # print("\n")

        if plTrue(cnf.cnf(combine('and', kb.clause)), model):
            return plTrue(alphaCnf, model)
        else:
            return True  # when KB is false, always return True
    else:
        p, rest = symbols[0], symbols[1:]
        return (tTCheckAll(kb, alpha, rest, modelExtend(model, p, True)) and tTCheckAll(kb, alpha, rest,
                                                                                        modelExtend(model, p, False)))


def plTrue(clause, model={}):
    '''
    Return True if the clause is true in the model, and False if it is false. 
    Return None if the model does not specify all symbols

    '''
    assert len(model) > 0, 'the length of model should be more than 0'
    assert len(clause) > 0, 'the length of clause should be more than 0'
    if type(clause) == str:
        return model[clause]
    elif len(clause) >= 2:  # must be the type of list
        if clause[0] == 'not':
            return not plTrue(clause[1], model)
        elif clause[0] == 'and':
            clauseRest = combine('and', clause[2:])
            if len(clauseRest) == 0:  # if operation is 'and', remove the influence of []
                return plTrue(clause[1], model)
            else:
                return plTrue(clause[1], model) and plTrue(clauseRest, model)
        elif clause[0] == 'or':
            clauseRest = combine('or', clause[2:])
            if len(clauseRest) == 0:
                return plTrue(clause[1], model)
            else:
                return plTrue(clause[1], model) or plTrue(clauseRest, model)


def propSymbols(clause):
    '''
    Return the list of all propositional symbols in cnfClause.

    '''
    if len(clause) == 0:
        return []
    elif type(clause) == str:
        return [clause]
    elif len(clause) <= 2:  # P or not P, just return self
        return [clause[-1]]
    else:
        rtSymbols = []
        for s in clause[1:]:
            pI = propSymbols(s)
            rtSymbols.extend(list(set(pI)))
        return list(set(rtSymbols))


def modelExtend(model, p, v):
    '''
    Return the new model with p values v added

    '''
    model2 = model.copy()
    model2[p] = v
    return model2


def plResolution(kb, alpha):
    '''
    returns if KB entailments alpha True or False using pl resolution
    kb: KnowledgeBase
    alpha: the result to prove

    '''
    clause = kb.clause + Split('and', cnf.cnf(negativeInside(alpha)))
    # print("clause:", clause)
    Generatedlist = []
    while True:
        n = len(clause)
        pairs = [(clause[i], clause[j]) for i in range(n) for j in range(i + 1, n)]
        for (ci, cj) in pairs:
            resolvents = plResolve(ci, cj)
           # print("After doing resolution for % s and %s we get %s" % (ci, cj, resolvents))
            if [] in resolvents:
                return True
            for tempCR in resolvents:
                if not tempCR in Generatedlist:
                    Generatedlist.append(tempCR)
            # Generatedlist = toUnique(Generatedlist + resolvents)
        #     print("Generatedlist:", Generatedlist)
        # print("clause:", clause)

        if isSublistOf(Generatedlist, clause):
            return False
        for cc in Generatedlist:
            if not cc in clause:
                clause.append(cc)
        # clause = toUnique(clause + Generatedlist)


gloVar = 0  # used to compute the excute times


def plResolve(ci, cj):
    '''
    returns all clause that can be obtained from clause ci and cj

    '''
    clause = []
    for di in Split('or', ci):
        for dj in Split('or', cj):
            if di == negativeInside(dj) or negativeInside(di) == dj:
                # global gloVar
                # print("times: ", gloVar)
                # gloVar += 1

                diNew = Split('or', ci)
                diNew.remove(di)
                djNew = Split('or', cj)
                djNew.remove(dj)
                # print("diNew:", diNew) 
                # print("djNew:", djNew) 
                dNew = diNew + djNew
                dNew = toUnique(dNew)
                # print("dNew:", dNew)
                toAddD = combine('or', dNew)
                # print("toAddD:", toAddD)
                clause.append(toAddD)
    return clause


def negativeInside(s):
    '''
    move negation sign inside s

    '''
    if type(s) == str:
        return ['not', s]
    elif s[0] == 'not':
        return s[1]
    elif s[0] == 'and':
        tempRet = ['or']
        for element in s[1:]:
            tempRet.append(negativeInside(element))
        return tempRet
    elif s[0] == 'or':
        tempRet = ['and']
        for element in s[1:]:
            tempRet.append(negativeInside(element))
        return tempRet


def toUnique(clause):
    '''
    return a clause list whose elements are unique


    '''
    if type(clause) == str:
        return clause
    if len(clause) == 0:
        return clause
    retclause = []

    strElementList = list(set([str(element) for element in clause]))

    for element2 in strElementList:
        if '[' in element2:
            retclause.append(eval(element2))
        else:
            retclause.append(element2)
    return retclause


def isSublistOf(l1, l2):
    '''
    return if l1 is sublist of l2

    '''
    for element in l1:
        if not element in l2:
            return False
    return True


if __name__ == "__main__":
   #P1 Modus Ponens
   # knowledgebase
   problem1 = ['and',
               'P',
               ['if', 'P', 'Q']
               ]
   Find1 = 'Q'
   kbP1 = KnowledgeBase()  # initial a new knowledgebase for problem1
   for clause in problem1[1:]:  # tell all the clause to kbP1
       kbP1.tell(clause)
   print("-------------------------------------------")
   print("KnowledgeBase for P1")
   print("-------------------------------------------")
   for c in kbP1.clause:  # print all the clause for kb1
       print(c)
   print("-------------------------------------------")
   print("\n")
   # using truth table to solve
   print("-------------------------------------------")
   print("Result Using truth table")
   print("-------------------------------------------")
   print("Result: %s is %s" % (Find1, tTEntails(kbP1, Find1)))
   print("-------------------------------------------")
   print("\n")
   # using pl resolution to solve
   print("-------------------------------------------")
   print("Result Using pl resolution")
   print("-------------------------------------------")
   print("Result: %s is %s" % (Find1, plResolution(kbP1, Find1)))
   print("-------------------------------------------")

   #P2 Wumpus world
   # knowledgebase
   problem2 = ['and',
               ['not', 'P11'],
               ['iff', 'B11', ['or', 'P12', 'P21']],
               ['iff', 'B21', ['or', 'P11', 'P22', 'P31']],
               ['not', 'B11'],
               'B21'
               ]
   Find2 = ['not', 'P12']
   kbP2 = KnowledgeBase()
   for clause in problem2[1:]:
       kbP2.tell(clause)
   print("-------------------------------------------")
   print("KnowledgeBase for problem2")
   print("-------------------------------------------")      
   for c in kbP2.clause:
       print(c)
   print("-------------------------------------------")
   print("\n")
   # using truth table to solve
   print("-------------------------------------------")
   print("The result Using truth table")
   print("-------------------------------------------")
   print("Result: %s is %s" % (Find2, tTEntails(kbP2, Find2)))
   print("-------------------------------------------")
   print("\n")
   # using pl resolution to solve
   print("-------------------------------------------")
   print("Result Using pl resolution")
   print("-------------------------------------------")
   print("Result: %s is %s" % (Find2, plResolution(kbP2, Find2)))
   print("-------------------------------------------")

   #P3 The Doors of Enlightenment
   # knowledgebase
   problem3 = ['and',
               ['if', 'mythical', 'immortal'],
               ['if', ['not', 'mythical'], ['and', 'mortal', 'mammal']],
               ['if', ['or', 'immortal', 'mammal'], 'horned'],
               ['if', 'horned', 'magical']
           ]
   Find3a = 'mythical'
   Find3b = 'magical'
   Find3c = 'horned'
   kbP3 = KnowledgeBase()
   for clause in problem3[1:]:
        kbP3.tell(clause)
   print("-------------------------------------------")      
   print("KnowledgeBase for problem3")
   print("-------------------------------------------")      
   for c in kbP3.clause:
       print(c)
   print("-------------------------------------------")
   print("\n")
   # # using truth table to solve
   print("-------------------------------------------")      
   print("Result Using truth table")
   print("-------------------------------------------")      
   print("Result: %s is %s" % (Find3a, tTEntails(kbP3, Find3a)))
   print("Result: %s is %s" % (Find3b, tTEntails(kbP3, Find3b)))
   print("Result: %s is %s" % (Find3c, tTEntails(kbP3, Find3c)))
   print("-------------------------------------------")      
   print("\n")
   # # using pl resolution to solve
   print("-------------------------------------------")
   print("Result Using pl resolution")
   print("-------------------------------------------")      
   print("Result: %s is %s" % (Find3a, plResolution(kbP3, Find3a)))
   print("Result: %s is %s" % (Find3b, plResolution(kbP3, Find3b)))
   print("Result: %s is %s" % (Find3c, plResolution(kbP3, Find3c)))
   print("-------------------------------------------")



   #  P4 The doors of enlightenment 
   # knowledgebase
   problem4a = ['and',
                ['if', 'A', 'X'],
                ['if', ['not','A'], ['not', 'X']],
                ['if', 'B', ['or', 'Y', 'Z']],
                ['if', ['not','B'], ['not', ['or', 'Y', 'Z']]],
                ['if', 'C', ['and', 'A', 'B']],
                ['if', ['not','C'], ['not', ['and', 'A', 'B']]],
                ['if', 'D', ['and', 'X', 'Y']],
                ['if', ['not','D'], ['not', ['and', 'X', 'Y']]],
                ['if', 'E', ['and', 'X', 'Z']],
                ['if', ['not','E'], ['not', ['and', 'X', 'Z']]],
                ['if', 'F', ['or', 'D', 'E']],
                ['if', ['not','F'], ['not', ['or', 'D', 'E']]],
                ['if', 'G', ['if', 'C', 'F']],
                ['if', ['not','G'], ['not', ['if', 'C', 'F']]],
                ['if', 'H', ['if', ['and', 'G', 'H'], 'A']],
                ['if', ['not','H'], ['not', ['if', ['and', 'G', 'H'], 'A']]]
            ]
   Find4a = 'A'
   Find4b = 'B'
   Find4c = 'C'
   Find4d = 'D'
   Find4e = 'E'
   Find4f = 'F'
   Find4g = 'G'
   Find4h = 'H'
   Find4x = 'X'
   Find4y = 'Y'
   Find4z = 'Z'
   kbP4a = KnowledgeBase()
   for clause in problem4a[1:]:
        kbP4a.tell(clause)
   print("-------------------------------------------")
   print("KnowledgeBase for problem4a")
   print("-------------------------------------------")
   for c in kbP4a.clause:
       print(c)
   print("-------------------------------------------")
   print("\n")
   # # using truth table to solve
   print("-------------------------------------------")
   print("Result Using truth table")
   print("-------------------------------------------")
   print("Result: %s is %s" % (Find4a, tTEntails(kbP4a, Find4a)))
   print("Result: %s is %s" % (Find4b, tTEntails(kbP4a, Find4b)))
   print("Result: %s is %s" % (Find4c, tTEntails(kbP4a, Find4c)))
   print("Result: %s is %s" % (Find4d, tTEntails(kbP4a, Find4d)))
   print("Result: %s is %s" % (Find4e, tTEntails(kbP4a, Find4e)))
   print("Result: %s is %s" % (Find4f, tTEntails(kbP4a, Find4f)))
   print("Result: %s is %s" % (Find4g, tTEntails(kbP4a, Find4g)))
   print("Result: %s is %s" % (Find4h, tTEntails(kbP4a, Find4h)))
   print("Result: %s is %s" % (Find4x, tTEntails(kbP4a, Find4x)))
   print("Result: %s is %s" % (Find4y, tTEntails(kbP4a, Find4y)))
   print("Result: %s is %s" % (Find4z, tTEntails(kbP4a, Find4z)))
   print("-------------------------------------------")
   print("\n")
   # # using pl resolution to solve
   print("-------------------------------------------")
   print("Result Using pl resolution")
   print("-------------------------------------------")
   
   '''
   The False result takes too long to run so we did not include in the result
   '''
   
   print("Result: %s is %s" % (Find4a, plResolution(kbP4a, Find4a)))
   #print("Result: %s is %s" % (Find4b, plResolution(kbP4a, Find4b)))
   #print("Result: %s is %s" % (Find4c, plResolution(kbP4a, Find4c)))
   #print("Result: %s is %s" % (Find4d, plResolution(kbP4a, Find4d)))
   #print("Result: %s is %s" % (Find4e, plResolution(kbP4a, Find4e)))
   #print("Result: %s is %s" % (Find4f, plResolution(kbP4a, Find4f)))
   #print("Result: %s is %s" % (Find4g, plResolution(kbP4a, Find4g)))
   print("Result: %s is %s" % (Find4h, plResolution(kbP4a, Find4h)))
   print("Result: %s is %s" % (Find4x, plResolution(kbP4a, Find4x)))
   #print("Result: %s is %s" % (Find4y, plResolution(kbP4a, Find4y)))
   #print("Result: %s is %s" % (Find4z, plResolution(kbP4a, Find4z)))
   print("\n")
   
   # knowledgebase

   problem4b = ['and',
                ['if', 'A', 'X'],
                ['if', ['not','A'], ['not', 'X']],
                ['if', 'C', 'A'],
                ['if', ['not','C'], ['not', 'A']],
                ['if', 'G', ['or', ['if', 'C', 'AT'], ['if', 'C', ['not','AT']]]],
                ['if', ['not','G'], ['not', ['or', ['if', 'C', 'AT'], ['if', 'C', ['not','AT']]]]],
                ['if', 'H', ['if', ['and', 'G', 'H'], 'A']],
                ['if', ['not','H'], ['not', ['if', ['and', 'G', 'H'], 'A']]],
                'AT'   # always true
            ]
   kbP4b = KnowledgeBase()
   for clause in problem4b[1:]:
        kbP4b.tell(clause)
   print("-------------------------------------------")
   print("KnowledgeBase for problem4b")
   print("-------------------------------------------")
   for c in kbP4b.clause:
       print(c)
   print("-------------------------------------------")
   print("\n")
   # # using truth table to solve
   print("-------------------------------------------")
   print("The result Using truth table")
   print("-------------------------------------------")
   print("Result: %s is %s" % (Find4a, tTEntails(kbP4b, Find4a)))
   print("Result: %s is %s" % (Find4b, tTEntails(kbP4b, Find4b)))
   print("Result: %s is %s" % (Find4c, tTEntails(kbP4b, Find4c)))
   print("Result: %s is %s" % (Find4d, tTEntails(kbP4b, Find4d)))
   print("Result: %s is %s" % (Find4e, tTEntails(kbP4b, Find4e)))
   print("Result: %s is %s" % (Find4f, tTEntails(kbP4b, Find4f)))
   print("Result: %s is %s" % (Find4g, tTEntails(kbP4b, Find4g)))
   print("Result: %s is %s" % (Find4h, tTEntails(kbP4b, Find4h)))
   print("Result: %s is %s" % (Find4x, tTEntails(kbP4b, Find4x)))
   print("Result: %s is %s" % (Find4y, tTEntails(kbP4b, Find4y)))
   print("Result: %s is %s" % (Find4z, tTEntails(kbP4b, Find4z)))
   print("\n")
 
   # # using pl resolution to solve
   print("-------------------------------------------")
   print("Result Using pl resolution")
   print("-------------------------------------------")
   print("Result: %s is %s" % (Find4a, plResolution(kbP4b, Find4a)))
   #print("Result: %s is %s" % (Find4b, plResolution(kbP4b, Find4b)))
   #print("Result: %s is %s" % (Find4c, plResolution(kbP4b, Find4c)))
   #print("Result: %s is %s" % (Find4d, plResolution(kbP4b, Find4d)))
   #print("Result: %s is %s" % (Find4e, plResolution(kbP4b, Find4e)))
   #print("Result: %s is %s" % (Find4f, plResolution(kbP4b, Find4f)))
   print("Result: %s is %s" % (Find4g, plResolution(kbP4b, Find4g)))
   print("Result: %s is %s" % (Find4h, plResolution(kbP4b, Find4h)))
   print("Result: %s is %s" % (Find4x, plResolution(kbP4b, Find4x)))
   #print("Result: %s is %s" % (Find4y, plResolution(kbP4b, Find4y)))
   #print("Result: %s is %s" % (Find4z, plResolution(kbP4b, Find4z)))
   print("\n")
