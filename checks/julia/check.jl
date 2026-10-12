# Check of the construction of 3-good partitions of [n] = {1, ..., n} in Julia.
#
# For every n <= NMAX and for a list of larger n, the program builds the
# partition of [n] of Theorem 1.2 of the paper and checks that each part has at
# most three distinct elements, that its sum is a power of 3, and that the
# parts cover [n] exactly once.  It also checks the invariant H(n) of
# Proposition 4.1 wherever it applies.
#
# Usage: julia check.jl [NMAX]   (default 20000)

const Part = Vector{Int}

level(n::Int) = (t = 0; while 3^(t + 1) <= n; t += 1; end; t)

function ispow3(s::Int)
    s < 1 && return false
    while s % 3 == 0
        s ÷= 3
    end
    return s == 1
end

# Lemma 2.1: [-l, l], l mod 3 != 2, as {0} and zero-sum triples, mapped by x -> c + s x.
function zs_interval!(out::Vector{Part}, l::Int, c::Int, s::Int)
    @assert l >= 0 && l % 3 != 2
    if l % 3 == 0
        k = l ÷ 3
        push!(out, [c])
    else
        k = (l - 1) ÷ 3
        push!(out, [c - s * l, c, c + s * l])
    end
    for i in 0:k-1
        push!(out, [c - s * (3k - i), c + s * (1 + i), c + s * (3k - 1 - 2i)])
        push!(out, [c - s * (2k - i), c - s * (k - i), c + s * (3k - 2i)])
    end
    return out
end

# Lemma 3.2: the involution sigma_N of [1, 2N - 2].
function sigma(N::Int, x::Int)
    x == 1 && return N
    x == N && return 1
    x == 2 && return N + 1
    x == N + 1 && return 2
    if iseven(N)
        return x <= N - 1 ? x + N - 1 : x - (N - 1)
    end
    x == 2N - 3 && return 2N - 2
    x == 2N - 2 && return 2N - 3
    x == 3 && return N - 1
    x == N - 1 && return 3
    x == 4 && return N + 2
    x == N + 2 && return 4
    return x <= N - 2 ? x + N - 2 : x - (N - 2)
end

pairs_of(N::Int) = N == 1 ? Tuple{Int,Int}[] :
    [(z, sigma(N, z)) for z in 1:2N-2 if z < sigma(N, z)]

# The partition of Delta_N into {0} and zero-sum triples, mapped by x -> P + x.
function delta_parts!(out::Vector{Part}, N::Int, P::Int)
    if N == 1
        push!(out, [P])
    elseif iseven(N)
        M = N ÷ 2
        push!(out, [P + 4M - 2, P - 2M, P - (2M - 2)])
        zs_interval!(out, M - 2, P, 2)
    else
        M = (N - 1) ÷ 2
        push!(out, [P + 4M, P - (2M + 1), P - (2M - 1)])
        push!(out, [P + 4M - 4, P - 2M, P - (2M - 4)])
        zs_interval!(out, M - 3, P, 2)
    end
    return out
end

# Proposition 4.1: [1, n] minus {n - 1, n, 3^(t+1) - 2n + 1}.
function hyp!(out::Vector{Part}, n::Int, t::Int)
    T = 3^t
    j = n - T
    @assert j % 3 == 2 && j >= 2 && 2j + 1 <= T
    inD = falses(T)
    if j == 2
        inD[3] = true
        push!(out, [3])
        push!(out, [T])
    else
        u = level(j)
        P = 3^(u + 1)
        if 3j > T || 2j + 1 <= P
            inD[1:j-2] .= true
            inD[2j-1] = true
            zs_interval!(out, j - 2, T, 1)
            if 3j > T
                hyp!(out, j, t - 1)
            else
                hyp!(out, j, u)
                push!(out, [P - 2j + 1, 2j - 1])
            end
        else
            N = j - (P - 1) ÷ 2
            e = P - 1 - j
            inD[1:e] .= true
            inD[P+2N-2] = true
            zs_interval!(out, e, T, 1)
            for (z, w) in pairs_of(N)
                inD[P+z+w-(2N+1)] = true
                push!(out, [T + e + z, T + e + w, T - (2e + z + w)])
            end
            part!(out, e)
            delta_parts!(out, N, P)
        end
    end
    for x in 1:(T-1)÷2
        if !inD[x] && !inD[T-x]
            push!(out, [x, T - x])
        end
    end
    return out
end

function part!(out::Vector{Part}, n::Int)
    n == 0 && return out
    n == 1 && return push!(out, [1])
    n == 2 && return push!(out, [1, 2])
    t = level(n)
    T = 3^t
    if n == T
        part!(out, T - 1)
        return push!(out, [T])
    end
    if 2n >= 3T + 1
        a = 3T - 1 - n
        part!(out, a)
        for x in a+1:(3T-1)÷2
            push!(out, [x, 3T - x])
        end
        return out
    end
    j = n - T
    if j % 3 != 2
        part!(out, T - j - 1)
        return zs_interval!(out, j, T, 1)
    end
    hyp!(out, n, t)
    return push!(out, [n - 1, n, 3T - 2n + 1])
end

function verify(ps::Vector{Part}, n::Int, skip::Vector{Int}, label::String)
    seen = falses(n)
    for s in skip
        seen[s] = true
    end
    covered = 0
    for p in ps
        (1 <= length(p) <= 3) || error("$label: part size $(p)")
        for x in p
            (1 <= x <= n && !seen[x]) || error("$label: element $x out of range or repeated")
            seen[x] = true
            covered += 1
        end
        ispow3(sum(p)) || error("$label: sum of $(p) is not a power of 3")
    end
    covered + length(skip) == n || error("$label: not a cover")
end

function main()
    nmax = length(ARGS) >= 1 ? parse(Int, ARGS[1]) : 20000
    count_h = 0
    for n in 1:nmax
        verify(part!(Part[], n), n, Int[], "n = $n")
        t = level(n)
        T = 3^t
        j = n - T
        if t >= 1 && j % 3 == 2 && j >= 2 && 2j + 1 <= T
            verify(hyp!(Part[], n, t), n, [n - 1, n, 3T - 2n + 1], "H($n)")
            count_h += 1
        end
    end
    println("Theorem 1.2: 3-good partitions of [n] for all n <= $nmax: ok")
    println("Proposition 4.1: invariant H(n) for the $count_h values n <= $nmax where it applies: ok")
    big = [3^12 + 2, 3^12 + 3^10 + 3^8 + 2, 3^13 + (3^11 - 1) ÷ 2 + 2, 3^14 + 3^13 ÷ 2, 5_000_011]
    for n in big
        verify(part!(Part[], n), n, Int[], "n = $n")
    end
    println("Theorem 1.2: $(length(big)) larger values of n up to $(maximum(big)): ok")
    println("Julia check passed.")
end

main()
