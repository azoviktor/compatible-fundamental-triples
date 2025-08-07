using LinearAlgebra

# Function to compute minor of matrix A by removing row i and column j
function minor(A, i, j)
    A[setdiff(1:end, i), setdiff(1:end, j)]
end

minor(F[:,:,1], 1, 2)

# Function to compute cofactor matrix
function cofactor_matrix(A::AbstractMatrix)
    n = size(A, 1)
    T = Polynomial{Commutative{CreationOrder}, Graded{LexOrder}, ComplexF64}
    C = Matrix{T}(undef, n, n)
    for i in 1:n
        for j in 1:n
            C[i, j] = (-1)^(i + j) * det(minor(A, i, j))
        end
    end
    return C
end

cofactor_matrix(F[:,:,1])

# Function to compute adjugate matrix
function adjugate(A)
    return Matrix(transpose(cofactor_matrix(A)))
end

adjugate(F[:,:,1])
