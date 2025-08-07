function q2sR(q)
    a,b,c,d = q
    return [a^2+b^2-c^2-d^2 2*(b*c-a*d) 2*(b*d+a*c);
            2*(b*c+a*d) a^2-b^2+c^2-d^2 2*(c*d-a*b);
            2*(b*d-a*c) 2*(c*d+a*b) a^2-b^2-c^2+d^2]
end

function q2R(q)
    a,b,c,d = q
    return 1/(a^2+b^2+c^2+d^2)*q2sR(q)
end

rand_rotation() = q2R(randn(4))

struct Samples{V<:Variable, T<:Number}
    vars::Vector{V}
    samples::Matrix{T}
end

samples(S::Samples) = S.samples
samples(S::Samples, i::Int) = S.samples[:, i]
nsamples(S::Samples) = size(S.samples, 2)

function random_triplet_ess()
    R = [rand_rotation() for _ in 1:3]
    C = [rand(Float64, 3) for _ in 1:3]
    return vcat([(rand(Float64)*R[i]*xx(C[i]-C[j])*R[j]')[:] for (i,j) in [(1,2), (2,3), (3,1)]]...)
end

function triplet_ess_samples(nsamples::Int, vars::Vector{V}) where {V<:Variable}
    M = zeros(ComplexF64, length(vars), nsamples)
    for i in 1:nsamples
        M[:, i] = random_triplet_ess()
    end
    return Samples(vars, M)
end

