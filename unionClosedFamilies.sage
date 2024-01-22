# Parameterized UC Family Constructors ###########################################################################

# makes a family with minimal singletons {1}, {2}, {3}, ..., {n}
def makeSingletonFamily(n,nullFree=True):
    return makeKFamily(n,1,nullFree)

# makes the family with overlapping minimal pairs {1,2}, {2,3}, {3,4}, ... {n-1,n}
def makePairFamily(n,nullFree=True):
    return makeKFamily(n,2,nullFree)

# makes the family with overlapping minimal triples {1,2,3}, {2,3,4}, ... {n-2,n-1,n}
def makeTripleFamily(n,nullFree=True):
    return makeKFamily(n,3,nullFree)

# makes the family with minimal consisting of overlapping k-tuples from [1..n]
def makeKFamily(n,k,nullFree=True):
    base = []
    for i in range(1,n-(k-2)):
        base.append(Set([i..i+(k-1)]))
    if not nullFree:
        base.append(Set())
    return makeUnionClosedFamily(base,nullFree)

# makes the family with minimal consisting of all possible triples from [1..n]
def makeAllTriplesFamily(n,nullFree=True):
    return makeAllKFamily(n,3,nullFree)

# makes the family with minimal consisting of all possible k-tuples from [1..n]
def makeAllKFamily(n,k,nullFree=True):
    base = list(map(Set, itertools.combinations([1..n], k)))
    return makeUnionClosedFamily(base,nullFree=True)

# makes the family with incremental minimal {1}, {1,2}, {1,2,3}, {1,2,3,4}, ... {1,...,n}
def makeIncrementalFamily(n):
    base = []
    for i in range(1,n+1):
        base.append(Set([1..i]))
    return makeUnionClosedFamily(base)

# if n is not even, it will be set to the next even number
# makes the family with disjoint minimal pairs {1,2}, {3,4}, {5,6}, ... {n-1,n}
def makeDisjointPairFamily(n):
    return makeDisjointKFamily(n,2)

# if n is not a multiple of 3, it will be set to the next multiple of 3
# makes the family with disjoint minimal triples {1,2,3}, {4,5,6}, {7,8,9}, ... {n-2,n-1,n}
def makeDisjointTripleFamily(n):
    return makeDisjointKFamily(n,3)

# if n is not a multiple of k, it will be set to the next multiple of k
# makes the family with disjoint minimal k-tuples {1,2,3, ... k}, {k+1, ... 2k+1}, {2k+2, ... 3k}, ... {... n}
def makeDisjointKFamily(n,k):
    base = []
    i = 1
    if n % k != 0:
        n += 1
    while i < n-(k-2):
        base.append(Set([i..i+(k-1)]))
        i += k
    return makeUnionClosedFamily(base)

# if n is not a triangular number, it will be set to the next triangular number
# makes the family with disjoint incremental minimal {1}, {2,3}, {4,5,6}, {7,8,9,10}, {11,12,13,14,15}, ... {... n}
def makeDisjointIncrementalFamily(n):
    base = []
    n = findNearestTriangular(n)
    # for each i, add [i..i+j] to the base
    i = 1
    j = 0
    while i <= n:
        base.append(Set[i..i+j])
        i += j+1
        j += 1
    return makeUnionClosedFamily(base)

# makes the family with minimal sets each missing one elements from [n]
# for n=4, this is {1,2,3}, {1,2,4}, {1,3,4}, {2,3,4}
def missingOne(n):
    return missingK(n,1)

# makes the family with minimal sets each missing k elements from [n]
def missingK(n,k):
    if n <= k:
        return [Set()]
    base = []
    missing = list(map(Set, itertools.combinations([1..n], k)))
    for m in missing:
        base.append(Set[1..n] - m)
    return makeUnionClosedFamily(base)

# makes the family with minimal sets each missing one element from [n] truncated to the first m missing elements
# the family is generated in the order: the set missing n, missing n-1, missing n-2, missing n-3, ... missing 1
def missingOneTruncated(n, m=-1):
    if m == -1:
        return missingOne(n)
    base = []
    for i in range(1,m+1):
        base.append(Set[1..n] - Set([n-i+1]))
    return base

# creates a UC set family of height h, width w, and size (h + w - 1)
def makeAnyHeightWidth(h,w):
    return makeAnyHeightWidthSize(h,w,s=-1)

# creates a UC set family of height h, width w, and size h+w-1 <= s <= w*(h-1)+1
# if the chosen value of s is outside of the valid range, s is clamped to a valid value
def makeAnyHeightWidthSize(h, w, s=-1):
    base = []
    s = clamp(s, h+w-1, w*(h-1)+1)
    if w == 1:
        for i in range(2,h+2):
            base.extend(missingOneTruncated(i,1))
        return base
    rowSizes = [0]*h
    rowSizes[h-1] = 1
    rowSizes[0] = w
    s -= 1+w
    while s > 0:
        for j in range(1,min(s+1,h-1)):
            rowSizes[j] += 1
            s -= 1
    for i in range(0,h):
        rowSize = rowSizes[i]
        base.extend(missingOneTruncated(w+i, rowSize))
    return base

# Creates the Hungarian family on n sets
# p2062-2063 of Bruhn and Schaudt 2015
# The Hungarian family, H(n), is the initial segment of length n of the set of finite subsets sorted with the Hungarian comparison
# # H(n) is a subset of [ceil(log2(n))]
# The Hungarian comparison is A < B if:
# max(A) < max(B) or
# max(A) = max(B) and max(A ^ B) in A (where A ^ B is the XOR operation)
def hungarianFamily(n):
    #the smallest valid n for the hungarian family is 1
    n = max(1,n)
    # I couldn't find a more efficient way to implement the comparator than cmp_to_key
    return sorted(makeSingletonFamily(ceil(math.log2(n)),nullFree=False), key=functools.cmp_to_key(hungarianComparison))[0:n]

# Creates the Renaud-Fitina family on n sets
# p2070-2071 of Bruhn and Schaudt 2015
# The Renaud-Fitina family, R(n), is the initial segment of length n of the set of finite subsets sorted with the Renaud-Fitina comparison
# The Renaud-Fitina comparison is A < B if:
# max(A) < max(B) or
# max(A) = max(B) and |A| > |B| or
# max(A) = max(B) and |A| = |B| and max(A ^ B) in B
# where ^ denotes XOR
def renaudFitinaFamily(n):
    n = max(1,n)
    return sorted(makeSingletonFamily(findRenaudFitinaK(n),nullFree=False),key=functools.cmp_to_key(renaudFitinaComparison))[0:n]

# create the powerset on groundset [n] then remove the bottom m rows
def makeSlicedPowerset(n,m):
    F = makeSingletonFamily(n)
    for s in range(1,m+1):
        for f in getRow(F,s):
            F.remove(f)
    return F

# Conjecturing Families ###########################################################################

twoSingleton = makeUnionClosedFamily([Set([1]),Set([2])])

#ce to: numberOfMostCommonElement(x) >= maxF(x)
onePair = makeUnionClosedFamily([Set([1,2])])
# onePair.name(new = "onePair")

twoSingletonAndTwin = makeUnionClosedFamily([Set([1]),Set([2]),Set([3,4])])
# twoSingletonAndTwin.name(new = "twoSingletonAndTwin")


#ce to: numberOfMostCommonElement(x) >= maxDegree(x)
CE1 = makeUnionClosedFamily([Set([1,2]),Set([3,2]),Set([3,4]),Set([5,4])]) #note: only need to specify minimal elements
# CE1.name(new = "CE1")

# example where {1,2,3} is a set but none of 1,2,3 is in half of the sets
# https://mathworld.wolfram.com/Union-ClosedSetsConjecture.html
# https://mathoverflow.net/questions/138567/renaud-sarvate-limitation-on-frankls-conjecture/228124#228124
CE2 = [Set([1,2,3]), Set([1,2,3,6,7,8,9]), Set([1,2,3,4,6,7,8,9]), Set([1,2,3,4,5,6,7,8,9]), Set([1,2,3,4,5,8,9]), Set([1,2,3,4,5,6,8,9]), Set([1,2,3,4,5,6,7]), Set([1,2,3,4,5,6,7,8]), Set([6,7,8,9]), Set([4,6,7,8,9]), Set([4,5,6,7,8,9]), Set([4,5,8,9]), Set([4,5,6,8,9]), Set([4,5,6,7]), Set([4,5,6,7,8]), Set([1,6,7,8,9]), Set([1,4,6,7,8,9]), Set([1,4,5,6,7,8,9]), Set([2,4,5,8,9]), Set([2,4,5,6,8,9]), Set([2,4,5,6,7,8,9]), Set([3,4,5,6,7]), Set([3,4,5,6,7,8]), Set([3,4,5,6,7,8,9]), Set([1,2,4,5,6,7,8,9]), Set([1,3,4,5,6,7,8,9]), Set([2,3,4,5,6,7,8,9])]
# CE2.name(new = "CE2")

#ce to: height >= width
# any family in makeDisjointIncrementalFamily with n >= 10
# any family in missingOne with n >= 4
CE3 = makeDisjointIncrementalFamily(15)
# CE3.name(new = "CE3")

CE4 = missingOne(6)
# CE4.name(new = "CE4")
#ce to: cardMostCommonElement(x) >= width(x)

#ce to: cardMostCommonElement(x) >= familySize(x) - width(x)
# any singleton family with n >= 3
CE5 = makeSingletonFamily(5)
#CE5.name(new = "CE5")

#ce to: cardMostCommonElement(x) >= minCardSet(x)^(width(x) - 1)
CE6 = makeSingletonFamily(6)
#CE6.name(new = "CE6")
# any family in missingOne with n >= 2
# CE4 already listed above

# ce to: maxFrequency(x) >= (minExpansionFrequency(x) - 1)*minCardSet(x)
CE7 = makeUnionClosedFamily([Set([1,2]),Set([3,4]),Set([5,6])])

# non-counterexamples used for building conjectures
column3 = makeAnyHeightWidth(h=3,w=1)

larson8 = [Set([1,2,3,4]), Set([1,2,4,5]), Set([1,2,3,4,5])]

moreNormalFamilies = []
for n in range(5,30):
    if not math.log(2*n).is_integer():
        moreNormalFamilies.append(normalize(hungarianFamily(2*n)))
slicedPowerset = makeSlicedPowerset(5,2)
slicedPowerset2 = makeSlicedPowerset(5,3)

# Known theory: https://en.wikipedia.org/wiki/Union-closed_sets_conjecture
# families of at most 46 sets
# families of sets whose union has at most 11 eleemnts
# families of sets in which the smallest set has 1 or 2 elements
UCFamilies = [twoSingleton, onePair, twoSingletonAndTwin, CE1, CE2, CE3, CE4, CE5, CE6, CE7, hungarianFamily(6), column3, slicedPowerset, slicedPowerset2, larson8]
UCFamilies.extend(moreNormalFamilies)

