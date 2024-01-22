# Utilities for Creating TikZ diagrams

def toIntegerPoset(F):
    intSets = []
    for S in F:
        intSets.append(setToInt(S))
    return Poset((intSets,integerPosetCompare))

def intToSet(n):
    return Set(int(d) for d in str(n))

def setToInt(S):
    nList = list(S)
    nList.sort()
    s = ''
    for d in nList:
        s += str(d)
    return s

def integerPosetCompare(n,m):
    nSet = intToSet(n)
    mSet = intToSet(m)
    return nSet.issubset(mSet)

# General Math Utilities ###########################################################################

# since triangular numbers satisfy a=n(n+1)/2, 
# then n = ceil(1/2(sqrt(8a + 1) - 1)) gives the index of the next triangular number
# https://www.wolframalpha.com/input?i=a%3Dn%28n%2B1%29%2F2+find+n
# input: an integer
# output: the least triangular number greater than or equal to the input
def findNearestTriangular(a):
    n = ceil(0.5*(math.sqrt(8*a+1) - 1))
    return int(0.5*n*(n+1))

# https://stackoverflow.com/questions/4092528/how-to-clamp-an-integer-to-some-range#comment53230306_4092550
# https://en.wikipedia.org/wiki/Clamping_(graphics)
# input: a number n, a lower bound, and an upper bound
# output: n clamped between the lower and upper bounds
def clamp(n, smallest, largest):
    return max(smallest, min(n, largest))

# for given n, the RenaudFitina comparison needs k such that 2^(k-1) <= n < k
def findRenaudFitinaK(n):
    logn = math.log2(n)
    if logn.is_integer():
        return int(logn) + 1
    else:
        return ceil(logn)

# this function implements the Hungarian comparison
# The Hungarian comparison is A < B if:
# max(A) < max(B) or
# max(A) = max(B) and max(A ^ B) in A (where A ^ B is the XOR operation)
# input: two sets
# output: 0 if A==B, -1 if A < B, 1 if A > B
def hungarianComparison(A,B):
    # A = B
    if A == B:
        return 0
    # if one set is null
    if len(A) == 0:
        return -1
    if len(B) == 0:
        return 1
    # A < B
    if max(A) < max(B) or (max(A) == max(B) and max(A.symmetric_difference(B)) in A):
        return -1
    # A > B
    return 1

# this function implements the Renaud-Fitina comparison
# The Renaud-Fitina comparison is A < B if:
# max(A) < max(B) or
# max(A) = max(B) and |A| > |B| or
# max(A) = max(B) and |A| = |B| and max(A ^ B) in B
# where ^ denotes XOR
def renaudFitinaComparison(A,B):
    # A = B
    if A == B:
        return 0
    # if one set is null
    if len(A) == 0:
        return -1
    if len(B) == 0:
        return 1
    # A < B
    if max(A) < max(B) or (max(A) == max(B) and len(A) > len(B)) or (max(A) == max(B) and len(A) == len(B) and max(A.symmetric_difference(B)) in B):
        return -1
    # A > B
    return 1

# General Family Utilities ##########################################################################

import sage.combinat.designs.incidence_structures
def toIncidenceStructure(F):
    incidenceFamily = []
    for S in F:
        incidenceFamily.append(list(S))
    return IncidenceStructure(incidenceFamily)

def toPoset(F):
    return Poset((F,lambda x,y:x.issubset(y)))

def toReversePoset(F):
    return Poset((F,lambda x,y:y.issubset(x)))

def isElementIsomorphic(F,G):
    # element isomorphic uses incidence structure
    if not isinstance(F, IncidenceStructure):
        F = toIncidenceStructure(F)
    if not isinstance(G, IncidenceStructure):
        G = toIncidenceStructure(G)
    return F.is_isomorphic(G)

def isStructureIsomorphic(F,G):
    # structure isomorphic uses poset
    if not isinstance(F,sage.combinat.posets.posets.FinitePoset):
        F = toPoset(F)
    if not isinstance(G,sage.combinat.posets.posets.FinitePoset):
        G = toPoset(G)
    return F.is_isomorphic(G)

def addElementToFamily(F, x):
    for i in [0..len(F)-1]:
        currentSet = list(F[i])
        if x in currentSet:
            currentSet.append(x)
            F[i] = Set(currentSet)
    return F

def removeElementFromFamily(F, x):
    for i in [0..len(F)-1]:
        currentSet = list(F[i])
        if x in currentSet:
            currentSet.remove(x)
            F[i] = Set(currentSet)
    return F

def addElementToSet(F, setToUpdate, addElement):
    F.remove(setToUpdate)
    setToUpdate = list(setToUpdate)
    setToUpdate.append(addElement)
    F.append(Set(setToUpdate))
    return F

def removeElementFromSet(F, setToUpdate, subElement):
    F.remove(setToUpdate)
    setToUpdate = list(setToUpdate)
    setToUpdate.remove(subElement)
    F.append(Set(setToUpdate))
    return F

def getSupersets(F,S,strict=False):
    supers = []
    for A in F:
        if not strict:
            if S.issubset(A):
                supers.append(A)
        else:
            if S.issubset(A) and S != A:
                supers.append(A)
    return supers

# input: a set family
# output: a union closed set family, excluding {}
def makeUnionClosedFamily(F, nullFree = True):
    outF=copy(F)
    finished = False
    while not finished:
        check = False
        for T in outF:
            for S in F:
                temp = T.union(S)
                if not temp in outF:
                    outF.append(temp)
                    check = False
        if not check:
            finished = True
    # remove the empty set if it is present
    if nullFree and Set() in outF:
        outF.remove(Set())
    return outF

def makeIntersectionClosedFamily(F):
    outF = copy(F)
    finished = False
    while not finished:
        check = False
        for T in outF:
            for S in F:
                temp = T.intersection(S)
                if temp not in outF:
                    outF.append(temp)
                    check = False
        if not check:
            finished = True
    return outF

def makeDeltaClosedFamily(F):
    outF = copy(F)
    finished = False
    while not finished:
        check = False
        for T in outF:
            for S in F:
                temp = T.symmetric_difference(S)
                if temp not in outF:
                    outF.append(temp)
                    check = False
        if not check:
            finished = True
    return outF

def makeDeltaUnionClosedFamily(F):
    return makeDeltaClosedFamily(makeUnionClosedFamily(F, nullFree = True))

# all UC families are a subset of some family on some universe [n]
# the set [1..n] is the ground set of a set family
# input: a set family
# output: the ground set of elements of F
def Union(F):
    U = Set([])
    for S in F:
        U = U.union(S)
    return U

# prints the family F in order of set size: sets of size n, then n-1, ..., then size 1
def printFamily(F):
    for n in getSizeList(F):
        print(getRow(F, n))

# prints the number of sets of each size in F
def printFamilySizes(F):
    for n in getSizeList(F):
        print(f'{len(getRow(F,n))} sets of size {n}')

# this function returns the same thing as Union but is faster
# however, it requires that the ground set is an element of F
# input: a union-closed set family
# output: the ground set of elements in F
def groundSet(F):
    return max(F, key=len)

# this function is used as a helper function when reducing a family
# input: a union-closed set family
# output: the smallest integer not in F
def leastElementNotInFamily(F):
    ground = groundSet(F)
    minElement = min(ground)
    maxElement = max(ground)
    diff = Set[min(1, minElement)..maxElement] - ground
    # if diff is empty
    if not diff:
        return max(ground) + 1
    # else diff is not empty
    return min(diff)

# this function returns the blocks of F as a list of sets
# From Poonen, 1990:
# a block is an equivalence class of the relation ~ in which a ~ b iff Fa = Fb
# (in general, Fx is the set of sets in F which contain x)
def getBlocks(F):
    subsets = defaultdict(list)
    ground = groundSet(F)
    for x in ground:
        subsets[x] = containing(F, x)
    equivClasses = []
    classed = []
    for i in ground:
        if i not in classed:
            currentClass = Set(filter(lambda S: subsets[S] == subsets[i], subsets.keys()))
            equivClasses.append(currentClass)
            classed.extend(currentClass)
    return equivClasses

# inputs: a union-closed set family and a block in the family
# output: the set family in which the block has been replaced by a new singleton
#         the added singleton is the smallest number not present in F already
def replaceBlock(F, block):
    newElement = leastElementNotInFamily(F)
    toFixBlocks = []
    newFamily = []
    for S in F:
        if block.issubset(S):
            newFamily.append(S + Set([newElement]) - block)
        else:
            newFamily.append(S)
    return newFamily

# input: a union-closed set family where the ground set is not 1..n
# output: the input family but where the ground set is 1..n
def reduceFamily(F):
    least = leastElementNotInFamily(F)
    while leastElementNotInFamily(F) < max(groundSet(F)):
        F = replaceBlock(F, Set([max(groundSet(F))]))
    return F

# a family is Poonen-normalized if all blocks are singletons
# input: a union-closed set family
# output: the input family but Poonen normalized
def poonenNormalize(F):
    for b in getBlocks(F):
        if len(b) > 1:
            F = replaceBlock(F, b)
    return reduceFamily(F)

# we say an element is a minimal element of a family if none of its subsets are present in the family
# input: a UC set family and a set in the family
# output: if S is a minimal element in F, then returns True
#         if S is not a minimal element in F, then returns False and the subsets of S in F
def isMinimal(F, S):
    subsets = []
    for sub in F:
        if sub.issubset(S) and sub != S:
            subsets.append(sub)
    # if no subsets of S are in F, then S is a minimal element
    if not subsets:
        return True, subsets
    return False, subsets

# inputs: a family and a set in the family
# ouputs: if S is a union of minimal elements in F, then returns True
#         if S is not a union of minimal elements in F, then returns False and the set that needs to be added to the minimal of F
def isUnion(F, S):
    result, subsets = isMinimal(F, S)
    if result:
        return True, None
    # check if S is a union of elements which are subsets of it
    largestSub = Union(subsets)
    if largestSub == S:
        return True, None
    # S - largestSub is the set we need to add to the family to make S a union of smaller sets
    return False, S - largestSub

# a family is Larson-normalized if all sets in the family may be written as unions of minimal elements
# input: a union-closed set family 
# output: the input family after it has been Larson-normalized by adding minimal elements to it
def larsonNormalizeAdditive(F):
    newFamily = F
    for S in F:
        result, newSet = isUnion(F, S)
        # if a new set is needed, add it to the family
        if not result:
            newFamily.append(newSet)
    return makeUnionClosedFamily(newFamily)

# input: a union-closed set family
# output: the input family after it has been Larson-normalized by removing minimal elements
def larsonNormalizeSubtractive(F):
    newFamily = []
    for S in F:
        result, newSet = isUnion(F, S)
        # if an old set is not a union of minimal sets, remove it
        if result:
            newFamily.append(S)
    return makeUnionClosedFamily(newFamily)

def normalize(F):
    return poonenNormalize(larsonNormalizeSubtractive(F))

# input: a set family and an integer n
# output: the sets in F of cardinality n (the row of length n)
def getRow(F, n):
    sizeList = []
    for S in F:
        if len(S) == n:
            sizeList.append(S)
    return sizeList

# input: a set family and an element in the family
# output: the sets of F which contain x
def containing(F, x):
    return list(filter(lambda S: x in S, F))

# input: a set family and an element in the family
# output: the number of sets of F which contain x (|Fx|)
def frequency(F, x):
    return len(containing(F,x))

# input: a set family and an element in the family
# output: the ratio |Fx|/|F|
def abundance(F, x):
    return frequency(F, x)/len(F)

# an element x of F is abundant if |Fx|/|F| > 1/2
# if we were including the empty set in F, then it would be |Fx|/|F| >= 1/2
# Frankl's conjecture is that all UC families have an abundant element
# input: a set family and an element in the family
# output: a boolean for if |Fx|/|F| > 1/2
def isAbundant(F, x):
    return frequency(F, x) > len(F)/2

# if an element is not abundant, it is rare
# input: a UC set family and an element in the family
# output: a boolean for if x is not abundant in F
def isRare(F, x):
    return not isAbundant(F, x)

def expandFamilyOld(F):
    Fexpanded = copy(F)
    for x in groundSet(F):
        Fx = containing(Fexpanded, x)
        minimal = getMinimal(Fx)
        for S in minimal:
            # create a new element
            xNew = leastElementNotInFamily(Fexpanded)
            # for each set in Fexpanded which is a superset of S, add xNew
            updateSets = [S]
            updateSets.extend(getSupersets(Fexpanded, S, strict=True))
            for toUpdate in updateSets:
                Fexpanded = addElementToSet(Fexpanded, toUpdate, xNew)
        # after we have done all the additions, then remove x from all sets of Fexpanded
        Fexpanded = removeElementFromFamily(Fexpanded, x)
    return Fexpanded

def expandFamily(F):
    Fexpanded = copy(F)
    originalGround = groundSet(F)
    for x in originalGround:
        Fx = containing(Fexpanded, x)
        minimal = getMinimal(Fx)
        for S in minimal:
            exclS = excludeTuples(S)
            xNew = (x,exclS)
            updateSets = [S]
            updateSets.extend(getSupersets(Fexpanded, S, strict=True))
            for toUpdate in updateSets:
                Fexpanded = addElementToSet(Fexpanded, toUpdate, xNew)
    for x in originalGround:
        Fexpanded = removeElementFromFamily(Fexpanded, x)
    return Fexpanded

def contractFamily(Fexpanded):
    F = copy(Fexpanded)
    expandedGround = groundSet(Fexpanded)
    for x in expandedGround:
        Fx = containing(F, x)
        if isinstance(x, tuple):
            origEle = x[0]
            for S in Fx:
                F = addElementToSet(F, S, origEle)
            F = removeElementFromFamily(F, x)
    return F

def excludeTuples(S):
    excluded = []
    for ele in S:
        if not isinstance(ele,tuple):
            excluded.append(ele)
    return Set(excluded)

# if F is union closed and the output of this function is F, then Frankl has been disproved
# input: a UC set family
# output: the rare elements of F
def findRare(F):
    return groundSet(F) - findAbundant(F)

# input: a set family
# output: a list of the sizes of sets that appear in F
def getSizeList(F):
    sizeList = []
    for S in F:
        l = len(S)
        if l not in sizeList:
            sizeList.append(l)
    return sorted(sizeList, reverse=True)

# a row is the set of all sets in F which have the same cardinality
# the number of rows is the number of different cardinality sets appear in F
# input: a set family
# output: the number of rows in F
def rowNum(F):
    return len(getSizeList(F))

# input: a UC set family
# output: the element which appears in the most sets of F
def mostFrequentElement(F):
    return max(groundSet(F), key=functools.partial(frequency, F))

# input: a UC set family
# output: the element which appears in the least sets of F
def leastFrequentElement(F):
    return min(groundSet(F), key=functools.partial(frequency, F))

# if F is union closed and the output of this function is empty, then Frankl has been disproved
# input: a UC set family
# output: the abundant elements of F
def findAbundant(F):
    abun = []
    for x in groundSet(F):
        if isAbundant(F, x):
            abun.append(x)
    return abun

# input: a UC set family
# output: a list of the minimal sets
def getMinimal(F):
    minimal = []
    for S in F:
        if isMinimal(F, S)[0]:
            minimal.append(S)
    return minimal