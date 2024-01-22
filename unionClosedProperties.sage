# UC Set Family Properties ###########################################################################

# this function has the same running time as makeUnionClosedFamily, which is not ideal
# input: a set family
def isUnionClosed(F):
    nF = not Set([]) in F
    return makeUnionClosedFamily(F, nullFree=nF) == F

# this function has the same running time as makeDeltaClosedFamily, which is not ideal
# input: a set family
def isDeltaClosed(F):
    return makeDeltaClosedFamily(F) == F

def isIntersectionClosed(F):
    return makeIntersectionClosed(F) == F

def isDeltaUnionClosed(F):
    return isUnionClosed(F) and isDeltaClosed(F)

# input: a UC set family
# output: a boolean if F is Poonen-normal
def isPoonenNormal(F):
    return Set(poonenNormalize(F)) == Set(F)

# input: a UC set family
# output: a boolean if F is Larson-normal
def isLarsonNormal(F):
    return Set(larsonNormalizeSubtractive(F)) == Set(F)

def isMinimallyGenerated(F):
    return isLarsonNormal(F)

def isHDefectFree(F):
    while len(F) > 1:
        if not isMinimallyGenerated(F):
            return False
        minimal = getMinimal(F)
        F = list(set(F) - set(minimal))
    return True

# input: a UC set family
# output: a boolean if F is both Poonen- and Larson-normal
def isNormal(F):
    return isPoonenNormal(F) and isLarsonNormal(F)

def isFrankl(F):
    return len(findAbundant(F)) >= 1

def isPrincipal(F):
    for x in groundSet(F):
        Fx = containing(F,x)
        if not len(getMinimal(Fx)) == 1:
            return False
    return True

UCProperties = [isUnionClosed, isPoonenNormal, isLarsonNormal, isNormal, isFrankl, isPrincipal]