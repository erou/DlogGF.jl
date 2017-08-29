"""
# DlogGF

A library containing algorithms for computing discrete logarithm in finite
field.

# References

1. R. Barbulescu, P. Gaudry, A. Joux and E. Thomé: A quasi-polynomial algorithm
  for discrete logarithm in finite fields of small characteristic.
2. Stephen C. Pohlig and Martin E. Hellman: An Improved Algorithm for Computing
  Logarithms over GF(p) and Its Cryptographic Signifiance, IEEE transactions on
  information theory, vol. it-24, no. 1, January 1978.
3. Jincheng Zhuang and Qi Cheng: On Generating Coset Representatives of
  PGL_2(F-q) in PGL_2(F_q²)
4. R. Granger, T. Kleinjung and J. Zumbrägel: On the Powers of 2
"""
module DlogGF
using Nemo, Primes

function __init__()

    # Welcome message
    println("")
    print("Welcome to \n")
    print_with_color(:red, "                               
         8I  ,dPYb,                       
         8I  IP'`Yb                        
         8I  I8  8I                          .oooooo.    oooooooooooo   
         8I  I8  8'                         d8P'  `Y8b   `888'     `8  
   ,gggg,8I  I8 dP    ,ggggg,     ,gggg,gg 888            888         
  dP'  'Y8I  I8dP    dP'  'Y8ggg dP'  'Y8I 888            888oooo8     
 i8'    ,8I  I8P    i8'    ,8I  i8'    ,8I 888     ooooo  888    '     
 d8,   ,d8b,,d8b,_ ,d8,   ,d8'  d8,   ,d8I `88.    .88'   888           
 'Y8888P'`Y88P''Y88P'Y8888P'    'Y8888P'888  `Y8bood8P'   o888o           
                                      ,d8I'                              
                                    ,dP'8I                               
                                   ,8'  8I                               
                                   I8   8I                               
                                   `8, ,8I                               
                                    `Y8P'                             
")
end

# Basic functions

include("basics.jl")

# Random suite
include("random.jl")

# Linear algebra

include("linalg.jl")

# Generating the cosets

include("pglCosets.jl")

# Pohlig Hellman suite

include("pohligHellman.jl")

# Linear factors

include("linfactors.jl")

# BGJT algorithm

include("bgjt.jl")

# GKZ algorithm

include("gkz.jl")

# Factor base 

include("factorbase.jl")

# Debug

include("debug.jl")

# end of module
end
