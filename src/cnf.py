# cnf

def BiConElim(s):
    if type(s) is str:
        return s
    elif s[0] == "iff":
        return (["and",
                 ["if",
                  BiConElim(s[1]),
                  BiConElim(s[2])],
                 ["if",
                  BiConElim(s[2]),
                  BiConElim(s[1])]])
    else:
        return ([s[0]] + [BiConElim(i) for i in s[1:]])


def ImpliElim(s):
    if type(s) is str:
        return s
    elif s[0] == "if":
        return (["or",
                 ["not",
                  ImpliElim(s[1])],
                 ImpliElim(s[2])])
    else:
        return ([s[0]] + [ImpliElim(i) for i in s[1:]])


def MoveNegationIn1(s):
    if type(s) is str:
        return s
    elif s[0] == "not" and type(s[1]) is list and s[1][0] == "and":
        return (["or"] + [MoveNegationIn(["not", i]) for i in s[1][1:]])
    elif s[0] == "not" and type(s[1]) is list and s[1][0] == "or":
        return (["and"] + [MoveNegationIn(["not", i]) for i in s[1][1:]])
    else:
        return ([s[0]] + [MoveNegationIn(i) for i in s[1:]])


def MoveNegationIn(s):
    revision = MoveNegationIn1(s)
    if revision == s:
        return s
    else:
        return MoveNegationIn(revision)


def TwoNegElim(s):
    if type(s) is str:
        return s
    elif s[0] == "not" and type(s[1]) is list and s[1][0] == "not":
        return (TwoNegElim(s[1][1]))
    else:
        return ([s[0]] + [TwoNegElim(i) for i in s[1:]])


def IntoBinary(s):
    if type(s) is str:
        return s
    elif s[0] == "and" and len(s) > 3:
        return (["and", s[1], IntoBinary(["and"] + s[2:])])
    elif s[0] == "or" and len(s) > 3:
        return (["or", s[1], IntoBinary(["or"] + s[2:])])
    else:
        return ([s[0]] + [IntoBinary(i) for i in s[1:]])


def DistribOnBi(s):
    '''
    only works on binary connectives

    '''
    if type(s) is str:
        return s
    elif s[0] == "or" and type(s[1]) is list and s[1][0] == "and":
        # Distribute s[2] over s[1]
        return (["and"] + [Distrib(["or", i, s[2]]) for i in s[1][1:]])
    elif s[0] == "or" and type(s[2]) is list and s[2][0] == "and":
        # Distribute s[1] over s[2]
        return (["and"] + [Distrib(["or", i, s[1]]) for i in s[2][1:]])
    else:
        return ([s[0]] + [Distrib(i) for i in s[1:]])


def Distrib(s):
    revision = DistribOnBi(s)
    if revision == s:
        return s
    else:
        return Distrib(revision)


def andCombine(s):
    '''
    use and to combine

    '''
    revision = andCombine1(s)
    if revision == s:
        return s
    else:
        return andCombine(revision)


def andCombine1(s):
    if type(s) is str:
        return s
    elif s[0] == "and":
        result = ["and"]
        for i in s[1:]:
            if type(i) is list and i[0] == "and":
                result = result + i[1:]
            else:
                result.append(i)
        return result
    else:
        return ([s[0]] + [andCombine1(i) for i in s[1:]])


def orCombine(s):
    '''
    use or to combine

    '''
    revision = orCombine1(s)
    if revision == s:
        return s
    else:
        return orCombine(revision)


def orCombine1(s):
    if type(s) is str:
        return s
    elif s[0] == "or":
        result = ["or"]
        for i in s[1:]:
            if type(i) is list and i[0] == "or":
                result = result + i[1:]
            else:
                result.append(i)
        return result
    else:
        return ([s[0]] + [orCombine1(i) for i in s[1:]])


def duplicateLiteralsElination(s):
    if type(s) is str:
        return s
    if s[0] == "not":
        return s
    if s[0] == "and":
        return (["and"] + [duplicateLiteralsElination(i) for i in s[1:]])
    if s[0] == "or":
        remains = []
        for l in s[1:]:
            if l not in remains:
                remains.append(l)
        if len(remains) == 1:
            return remains[0]
        else:
            return (["or"] + remains)


def duplicateClausesElimination(s):
    if type(s) is str:
        return s
    if s[0] == "not":
        return s
    if s[0] == "or":
        return s
    if s[0] == "and":
        remains = []
        for c in s[1:]:
            if unique(c, remains):
                remains.append(c)
        if len(remains) == 1:
            return remains[0]
        else:
            return (["and"] + remains)


def unique(c, remains):
    for p in remains:
        if type(c) is str or type(p) is str:
            if c == p:
                return False
        elif len(c) == len(p):
            if len([i for i in c[1:] if i not in p[1:]]) == 0:
                return False
    return True


def cnf(s):
    s = BiConElim(s)
    s = ImpliElim(s)
    s = MoveNegationIn(s)
    s = TwoNegElim(s)
    s = IntoBinary(s)
    s = Distrib(s)
    s = andCombine(s)
    s = orCombine(s)
    s = duplicateLiteralsElination(s)
    s = duplicateClausesElimination(s)
    return s


if __name__ == "__main__":
    sentences = ['and',
                 ['not', 'P11'],
                 ['iff', 'B11', ['or', 'P12', 'P21']],
                 ['iff', 'B21', ['or', 'P11', 'P22', 'P31']],
                 ['not', 'B11'],
                 'B21',
                 'P12']
    test = ['and', 'P12', ['or', ['not', 'P12'], 'P21']]
    testand = ['and', 'P12', ['and', ['not', 'P12'], 'P21']]
    print(repr(cnf(testand)))