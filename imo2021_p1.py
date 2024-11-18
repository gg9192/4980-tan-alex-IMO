import math

def all_not_eq(a,b,c):
    return True if (a != b and a != c and b != c) else False


def is_perfect_square(n):
    if n < 0:
        return False
    root = math.isqrt(n)
    return root * root == n

def gen_triples(n):
    for a in range(n, (2 * n) + 1):
        for b in range(n, (2 * n) + 1):
            for c in range(n, (2 * n) + 1):
                if all_not_eq(a,b,c) and is_perfect_square(a + b) and is_perfect_square(a + c) and is_perfect_square(b + c):
                    return (a,b,c)
                
for i in range(100,107):
    print(gen_triples(i))
    