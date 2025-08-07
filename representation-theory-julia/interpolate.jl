using LinearAlgebra: nullspace

function evaluate_poly(f::Polynomial, S::Samples)
    return [f(S.vars => samples(S, i)) for i in 1:nsamples(S)]
end

function evaluate_hw_vectors(ic::IsotypicComponent, S::Samples)
    println("Evaluating highest weight vectors for isotypic component: ", highest_weight(ic))
    evals = zeros(ComplexF64, nsamples(S), mul(ic))
    for (i, irr) in enumerate(irreducibles(ic))
        f = vector(hw_vector(irr))
        eval = evaluate_poly(f, S)
        mₐ, mᵢ = maximum(abs, eval), minimum(abs, eval)
        if mₐ > 1000
            println(f)
        end
        println("Max in eval: ", mₐ)
        println("Min in eval: ", mᵢ)
        evals[:, i] = eval
    end
    return evals
end

function interpolate_constraints(
    ic::IsotypicComponent{A},
    vars::Vector{V};
    tol::Float64=1e-5
) where {A<:AbstractGroupAction{Lie}, V<:Variable}
    S = triplet_ess_samples(mul(ic), vars)
    M = evaluate_hw_vectors(ic, S)
    N = Matrix(transpose(nullspace(M; atol=tol)))
    size(N, 1) == 0 && return nothing
    rref!(N, tol)
    sparsify!(N, tol)
    hwvs = [sum(hw_vectors(ic; as_vectors=true) .* r) for r in eachrow(N)]
    hwvs = [div_by_smallest_coeff(hwv; tol=tol) for hwv in hwvs]
    return IsotypicComponent(
                action(ic),
                highest_weight(ic),
                [IrreducibleRepresentation(
                    action(ic),
                    HighestWeightModule(
                        action(ic),
                        WeightVector(highest_weight(ic), hwv)
                    )
                ) for hwv in hwvs]
    )
end

function interpolate_constraints(
    iso_decomp::IsotypicDecomposition{A, T, W, Ic},
    vars::Vector{V};
    tol::Float64=1e-5
) where {A<:AbstractGroupAction{Lie}, T<:GroupRepresentation{A}, W<:Weight, Ic<:IsotypicComponent, V<:Variable}
    constr_dict = Dict{W, Ic}()
    for ic in isotypics(iso_decomp)
        inter_ic = interpolate_constraints(ic, vars; tol=tol)
        !isnothing(inter_ic) && (constr_dict[highest_weight(ic)] = inter_ic)
    end
    return constr_dict
end