using DecomposingGroupRepresentations

@polyvar F[1:3, 1:3, 1:3]
SO3 = LieGroup("SO", 3)

# F[:,:,1] ∼ F₁₂, F[:,:,2] ∼ F₂₃, F[:,:,3] ∼ F₃₁
a₁ = MatrixGroupAction(SO3, vcat(eachcol(F[:,:,1]), eachrow(F[:,:,3])))
a₂ = MatrixGroupAction(SO3, vcat(eachcol(F[:,:,2]), eachrow(F[:,:,1])))
a₃ = MatrixGroupAction(SO3, vcat(eachcol(F[:,:,3]), eachrow(F[:,:,2])))

X = zeros(Int, 3, 27) # F₁ F₂ F₃
[X[i, 9*(i-1)+1:9*i] .= 1 for i in 1:3]
T = ScalingLieGroup(X)
a₄ = ScalingLieGroupAction(T, F[:])

a = a₁ × a₂ × a₃ × a₄ # Action of the reductive Lie group G


# ------------------- DEGREE 3 -------------------
V = FixedDegreePolynomials(F[:], 3)
ρ = GroupRepresentation(a, V)
irrs = irreducibles(ρ)
iso = isotypics(irrs)

include("samples.jl")
include("interpolate.jl")

# 7 isotypics
interp_ics = interpolate_constraints(iso, F[:]; tol=1e-10)

B₁ = basis(space(interp_ics[Weight([0,0,0,1,1,1])]))
B₂ = basis(space(interp_ics[Weight([0,0,0,3,0,0])]))
B₃ = basis(space(interp_ics[Weight([0,0,0,0,3,0])]))
B₄ = basis(space(interp_ics[Weight([0,0,0,0,0,3])]))
B₅ = basis(space(interp_ics[Weight([1,1,0,3,0,0])]))
B₆ = basis(space(interp_ics[Weight([0,1,1,0,3,0])]))
B₇ = basis(space(interp_ics[Weight([1,0,1,0,0,3])]))

using LinearAlgebra: tr, det
f = tr(F[:,:,1]*F[:,:,2]*F[:,:,3])
f + B₁[1] # B₁ is the trace constraint

# Determinant constraints
B₂[1] - det(F[:,:,1])
B₃[1] - det(F[:,:,2])
B₄[1] - det(F[:,:,3])

# Demazure constraints
dem1 = F[:,:,1]'*F[:,:,1]*F[:,:,1]' - 0.5*tr(F[:,:,1]'*F[:,:,1])*F[:,:,1]'
rref(vcat(B₅, dem1[:]))

dem2 = F[:,:,2]'*F[:,:,2]*F[:,:,2]' - 0.5*tr(F[:,:,2]'*F[:,:,2])*F[:,:,2]'
rref(vcat(B₆, dem2[:]))

dem3 = F[:,:,3]'*F[:,:,3]*F[:,:,3]' - 0.5*tr(F[:,:,3]'*F[:,:,3])*F[:,:,3]'
rref(vcat(B₇, dem3[:]))

B = vcat(B₁, B₂, B₃, B₄, B₅, B₆, B₇)
rrefB = rref(B);

# All constraints of degree 3
deg3 = vcat(B₁, B₂, B₃, B₄, B₅, B₆, B₇)


# ------------------- DEGREE 4 -------------------
V = FixedDegreePolynomials(F[:], 4)
ρ = GroupRepresentation(a, V)
irrs = irreducibles(ρ)
iso = isotypics(irrs)

# 51 isotypics
interp_ics = interpolate_constraints(iso, F[:]; tol=1e-12)

mulsDeg3 = [f*var for var in F[:] for f in deg3]
rref_mulsDeg3 = rref(mulsDeg3) # vector space Q, according to Section 3.1 from the paper

# Takes some time to compute
# Prints the weights [1,0,0,1,2,1], [0,1,0,1,1,2], [0,0,1,2,1,1]
for (hw, ic) in interp_ics
    B = basis(space(ic))
    polys = vcat(rref_mulsDeg3, B)
    rref_polys = rref(polys)
    if length(rref_polys) == length(rref_mulsDeg3) + length(B) # elements of B are not in Q
        println(hw)
    end
end

B₁ = basis(space(interp_ics[Weight([1,0,0,1,2,1])]))
B₂ = basis(space(interp_ics[Weight([0,1,0,1,1,2])]))
B₃ = basis(space(interp_ics[Weight([0,0,1,2,1,1])]))

deg4 = vcat(B₁, B₂, B₃)

include("adjugate.jl")

# constraints coming from (26)
F₁₂, F₂₃, F₃₁ = F[:,:,1], F[:,:,2], F[:,:,3]
F₂₁, F₃₂, F₁₃ = F[:,:,1]', F[:,:,2]', F[:,:,3]'
Ms = [
    F₁₂*adjugate(F₃₂)*F₃₁,
    F₃₁*adjugate(F₂₁)*F₂₃,
    F₂₁*adjugate(F₃₁)*F₃₂
]
idx = [([1,2], [2,1]), ([1,3], [3,1]), ([2,3], [3,2])]
symMs = [Ms[i][j₁...] - Ms[i][j₂...] for i in 1:length(Ms) for (j₁, j₂) in idx]

rref(vcat(deg4, symMs)) # vector spaces <deg4> and <symMs> are equal