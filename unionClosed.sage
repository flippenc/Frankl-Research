import itertools, functools
from collections import defaultdict
from math import inf
load("conjecturing.py")
load("unionClosedUtilities.sage")
load("unionClosedProperties.sage")
load("unionClosedFamilies.sage")

print("Loading UC famailies code. \n Invariants are in the list: UCInvariants. \n Families are in the list: UCFamilies. \n Properties are in the list: UCProperties.")

# UC Set Family Invariants ###########################################################################

# input: a set family
# output: the number of sets in the family
def familySize(F):
    return len(F)

# input: a set family
# output: the sum of the cardinalities of sets in F
def totalSize(F):
    total = 0
    for S in F:
        total += len(S)
    return total

# input: a set family
# output: the largest cardinality of a set in F
def maxCardSet(F):
    return len(max(F, key = len))

# input: a set family
# output: the smallest cardinality of a set in F
def minCardSet(F):
    return len(min(F, key = len))

# input: a set family
# output: the average cardinality of a set in F
def meanCardSet(F):
    return totalSize(F)/len(F)

# input: a UC set family
# output: the size of the ground set of F
def groundSetSize(F):
    return len(groundSet(F))

# input: a UC set family
# output: the number of minimal sets in F
def minimalSize(F):
    return len(getMinimal(F))

# input: a UC set family
# output: the ratio of number of minimal sets to the number of ground elements in F
def minimalDensity(F):
    return minimalSize(F)/groundSetSize(F)

# input: a UC set family
# output: the size of the intersection of all sets in F
def intersectionNumber(F):
    J = F[0]
    for i in range(1,len(F)):
        J = J.intersection(F[i])
    return len(J)

# input: a UC set family
# output: the minimum size of the intersection of any two minimal sets
def minMinimalIntersection(F):
    minInt = inf
    minimal = getMinimal(F)
    for A,B in itertools.combinations(F, 2):
        inter = len(A.intersection(B))
        if inter < minInt:
            minInt = inter
    return minInt

# input: a UC set family
# output: the maximum size of the intersection of any two minimal sets
def maxMinimalIntersection(F):
    maxInt = 0
    minimal = getMinimal(F)
    for A,B in itertools.combinations(F, 2):
        inter = len(A.intersection(B))
        if inter > maxInt:
            maxInt = inter
    return maxInt

# input: a UC set family
# output: the average size of the intersection of any two minimal sets
def meanMinimalIntersection(F):
    avg = 0
    total = 0
    minimal = getMinimal(F)
    for A,B in itertools.combinations(F, 2):
        avg += len(A.intersection(B))
        total += 1
    return avg/total

# input: a UC set family
# output: the frequency of the most frequent element in F
def maxFrequency(F):
    return frequency(F, mostFrequentElement(F))

# input: a UC set family
# output: the frequency of the least frequent element in F
def minFrequency(F):
    return frequency(F, leastFrequentElement(F))

def minMaxRatio(F):
    return minFrequency(F)/maxFrequency(F)

# input: a UC set family
# output: the average frequency of an element in F
def meanFrequency(F):
    avg = 0
    ground = groundSet(F)
    for x in ground:
        avg += frequency(F, x)
    return avg/len(ground)

def maxExpansionFrequency(F):
    return maxFrequency(expandFamily(F))

def minExpansionFrequency(F):
    return minFrequency(expandFamily(F))

def meanExpansionFrequency(F):
    return meanFrequency(expandFamily(F))

# input: a UC set family
# output: the abundance of the most abundant element in F
def maxAbundance(F):
    return maxFrequency(F)/len(F)

# input: a UC set family
# output: the abundance of the least abundant element in F
def minAbundance(F):
    return minFrequency(F)/len(F)

# input: a UC set family
# output: the average abundance of an element in F
def meanAbundance(F):
    return meanFrequency(F)/len(F)

# input: a UC set family
# output: the ratio between the number of abundant elements and the number of elements in the ground set
def abundanceRatio(F):
    return len(findAbundant(F))/len(groundSet(F))

# input: a UC set family
# output: the ratio between the number of rare elements and the number of elements in the ground set
def rareRatio(F):
    return len(findRare(F))/len(groundSet(F))

# input: a UC set family
# output: the size of the largest antichain in F
def width(F):
    # Poset(E,f): E is elements, f is the ordering: function f(x,y) where True -> x <= y and False -> x >= y
    # alternatively, ordering may be pairs [x,y] -> x <= y and [y,x] -> y <= x
    # lambda gives the set inclusion ordering
    # width is the size of the longest antichain
    # certificate = False returns just the width
    P=Poset((F,lambda x,y:x.issubset(y)))
    return P.width()

# input: a UC set family
# output: the size of the largest chain in F
def height(F):
    P=Poset((F,lambda x,y:x.issubset(y)))
    # height is number of elements in the longest chain, certificate=True returns (h,c), the height and the chain
    return P.height()

# alternatively, len(P.level_sets()) gives height and len(P.dilworth_decomposition()) gives width
# these are results of dilworth's and mirsky's theorems, respectively

UCInvariants = [familySize, totalSize, maxCardSet, minCardSet, meanCardSet, groundSetSize, minimalSize, minimalDensity,
                intersectionNumber, minMinimalIntersection, maxMinimalIntersection, meanMinimalIntersection,
                maxFrequency, minFrequency, meanFrequency, minMaxRatio,
                maxAbundance, minAbundance, abundanceRatio, rareRatio, width, height,
                maxExpansionFrequency, minExpansionFrequency, meanExpansionFrequency]

# UCProperties is defined in the unionClosedProperties file