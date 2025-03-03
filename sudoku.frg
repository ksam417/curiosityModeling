#lang forge/froglet 

abstract sig Boolean {}
one sig True, False extends Boolean {}

abstract sig Number {}
one sig ONE, TWO, THREE, FOUR, FIVE, SIX, SEVEN, EIGHT, NINE extends Number {}

// This is the definition of the sudoku board sig
sig Board {
    // Partial function from (Int,Int) to Int to get the integer on the board at some row and col 
    board: pfunc Int -> Int -> Number
}

// Predicate defining wellformedness of a Sudoku board 
pred wellformed[b: Board] {
    // Making sure that our board is a 9x9 size as we define for each row and col pair...
    all row, col: Int | {
        // everything outside of our 9x9 grid contains nothing
        (row < 0 or row > 8 or col < 0 or col > 8) implies {
            no b.board[row][col]
        }
    }
}

// Predicate defining what it means for the board to be empty
pred empty[b: Board] {
    // For every row and col pair...
    all row, col: Int | {
        // nothing exists in the cell 
        no b.board[row][col]
    }
}

// This predicate defines what it means for the Sudoku to be fill
pred fullBoard[b : Board]{
    // For all row and col integer pairings...
    all row, col: Int | {
        // if the row and col pair is valid (in the board) then...
        (row >= 0 and row <= 8 and col >= 0 and col <= 8) implies {
            // there is some value that is in that cell of the board
            some val : Number | {
                b.board[row][col] = val
            }
        }
    }
}

// Predicate defining what a valid col is in Sudoku
pred validCol[b: Board] {
    // For all row and col integer pairings...
    all row, col : Int |{
        // if the row and col pair is valid (in the board) then...
        (row >= 0 and row <= 8 and col >= 0 and col <= 8) implies {
            // there is some value in the board in the cell such that...
            let val = b.board[row][col] |

            (val != none) implies {
                // and there is not other row that is...
                no otherRow : Int | {
                    (otherRow >= 0 and otherRow <= 8)  
                    otherRow != row 
                    // valid, not equal to our current row, and has the same value as our current row + col pair
                    b.board[otherRow][col] = val    
                }
            }
        }
    }
}

// Predicate defining what a valid row is in Sudoku
pred validRow[b: Board] {
    // For all row and col integer pairings...
    all row, col : Int |{
        // if the row and col pair is valid (in the board) then...
        (row >= 0 and row <= 8 and col >= 0 and col <= 8) implies {

            // there is some value in the board in the cell such that...
            let val = b.board[row][col] |

            (val != none) implies {
                // and there is not other col that is...
                no otherCol : Int | {
                    // valid, not equal to our current col, and has the same value as our current row + col pair
                    (otherCol >= 0 and otherCol <= 8)  
                    otherCol != col 
                    b.board[row][otherCol] = val    
                }
            }
        }
    }
}


pred validSubGridsHelper[b: Board, rowRef : Int, colRef :Int]{
    no val : Number | {
        b.board[rowRef][colRef] = val
        or 
        b.board[rowRef][add[colRef, 1]] = val
        or 
        b.board[rowRef][add[colRef, 2]] = val
        or 
        b.board[add[rowRef,1]][colRef] = val
        or 
        b.board[add[rowRef,1]][add[colRef, 1]] = val
        or 
        b.board[add[rowRef,1]][add[colRef, 2]] = val
        or 
        b.board[add[rowRef,2]][colRef] = val
        or 
        b.board[add[rowRef,2]][add[colRef, 1]] = val
        or 
        b.board[add[rowRef,2]][add[colRef, 2]] = val
    }

}

pred validSubGrids[b: Board]{
    all row, col : Int {
        // Top left subgrid
        (row >= 0 and row <= 2 and col >= 0 and col <= 2) implies {
            validSubGridsHelper[b, 0, 0]
        }
        
        or 

        // Top middle subgrid
        (row >= 0 and row <= 2 and col > 2 and col <= 5) implies {
            validSubGridsHelper[b, 0, 3]
        }
        
        or 

        // Top right subgrid
        (row >= 0 and row <= 2 and col > 5 and col <= 8) implies {
            validSubGridsHelper[b, 0, 6]

        }
        
        or 

        // Mid left subgrid
        (row > 2 and row <= 5 and col >= 0 and col <= 2) implies {
            validSubGridsHelper[b, 3, 0]
        }
        
        or 

        // Mid middle subgrid
        (row > 2 and row <= 5 and col > 2 and col <= 5) implies {
            validSubGridsHelper[b, 3, 3]
        }
        
        or 


        // Mid right subgrid
        (row > 2 and row <= 5 and col > 5 and col <= 8) implies {
            validSubGridsHelper[b, 3, 6]
        }
        
        or 

        // Bottom left subgrid
        (row > 5 and row <= 8 and col >= 0 and col <= 2) implies {
            validSubGridsHelper[b, 6, 0]
        }
        
        or 

        // Bottom middle subgrid
        (row > 5 and row <= 8 and col > 2 and col <= 5) implies {
            validSubGridsHelper[b, 6, 3]
        }
        
        or 

        // Mid right subgrid
        (row > 5 and row <= 8 and col > 5 and col <= 8) implies {
            validSubGridsHelper[b, 6, 6]
        }
    }


}


run{
    some b : Board | {
        wellformed[b]
        fullBoard[b]
        validRow[b]
        validCol[b]
        validSubGrids[b]
    }
} for exactly 1 Board, 5 Int 


one sig SudokuGame {
    firstBoard: one Board,
    nextBoard: pfunc Board -> Board
}

pred placeNumber[prev: Board, r : Int, c: Int, post: Board] {

    no prev.board[r][c]


    (r >= 0 and r <= 8 and c >= 0 and c <= 8)

    some val : Number | {
        post.board[r][c] = val
    }

    validRow[post]
    validCol[post]
    validSubGrids[post]
    
    all r2, c2: Int | {
        (r2 != r or c2 != c) implies {
            post.board[r2][c2] = prev.board[r2][c2]
        }
    }
}


pred gameTrace {
    wellformed[SudokuGame.firstBoard] 
    empty[SudokuGame.firstBoard]

    all b: Board | {
        some SudokuGame.nextBoard[b] implies {
            some row, col: Int| {
                placeNumber[b, row, col, SudokuGame.nextBoard[b]]
            }
        }

    }
}


showAGame: run {
    gameTrace
} 
  for 20 Board, 5 Int for {nextBoard is linear}


/**

**/

// pred validSubGrids[b: Board]{
//     all row, col : Int | {
//         (row >= 0 and row <= 8 and col >= 0 and col <= 8) implies {
//             let val = b.board[row][col] |
//             (val != none) implies {
//                 let rowMod = remainder[row, 3] |
//                 let colMod = remainder[col, 3] |

//                 (rowMod = 0 and colMod = 0) implies {
//                     let row1 = add[row, 1] |
//                     let row2 = add[row, 2] |

//                     let col1 = add[col, 1] |
//                     let col2 = add[col, 2] |

//                     validSubGridHelper[b, val, row, col, row1, row2, col1, col2]
//                 } 

//                 or

//                 // row top position and col mid position
//                 (rowMod = 0 and colMod = 1) implies {
//                     let row1 = add[row, 1] |
//                     let row2 = add[row, 2] |

//                     let col1 = subtract[col, 1] |
//                     let col2 = add[col, 1] |

//                     validSubGridHelper[b, val, row, col, row1, row2, col1, col2]
//                 }

//                 or 

//                 // row top position and col bottom position
//                 (rowMod = 0 and colMod = 2) implies {
//                     let row1 = add[row, 1] |
//                     let row2 = add[row, 2] |

//                     let col1 = subtract[col, 1] |
//                     let col2 = subtract[col, 2] |

//                     validSubGridHelper[b, val, row, col, row1, row2, col1, col2]
//                 }

//                 or 

//                 // row mid position and col top position
//                 (rowMod = 1 and colMod = 0) implies {
//                     let row1 = subtract[row, 1] |
//                     let row2 = add[row, 1] |

//                     let col1 = add[col, 1] |
//                     let col2 = add[col, 2] |

//                     validSubGridHelper[b, val, row, col, row1, row2, col1, col2]
//                 }

//                 or 

//                 // row mid position and col mid position
//                 (rowMod = 1 and colMod = 1) implies {
//                     let row1 = subtract[row, 1] |
//                     let row2 = add[row, 1] |

//                     let col1 = subtract[col, 1] |
//                     let col2 = add[col, 1] |
            
//                     validSubGridHelper[b, val, row, col, row1, row2, col1, col2]
//                 }
                
//                 or 

//                 // row mid position and col bottom position
//                 (rowMod = 1 and colMod = 2) implies {
//                     let row1 = subtract[row, 1] |
//                     let row2 = add[row, 1] |

//                     let col1 = subtract[col, 1] |
//                     let col2 = subtract[col, 2] |

//                     validSubGridHelper[b, val, row, col, row1, row2, col1, col2]
//                 }

//                 or 

//                 // row bottom position and col top position
//                 (rowMod = 2 and colMod = 0) implies {
//                     let row1 = subtract[row, 1] |
//                     let row2 = subtract[row, 2] |

//                     let col1 = add[col, 1] |
//                     let col2 = add[col, 2] |

//                     validSubGridHelper[b, val, row, col, row1, row2, col1, col2]
//                 }

//                 or 

//                 // row bottom position and col mid position
//                 (rowMod = 2 and colMod = 1) implies {
//                     let row1 = subtract[row, 1] |
//                     let row2 = subtract[row, 2] |

//                     let col1 = subtract[col, 1] |
//                     let col2 = add[col, 1] |

//                     validSubGridHelper[b, val, row, col, row1, row2, col1, col2]
//                 }

//                 or 

//                 // row bottom position and col bottom position
//                 (rowMod = 2 and colMod = 2) implies {
//                     let row1 = subtract[row, 1] |
//                     let row2 = subtract[row, 2] |

//                     let col1 = subtract[col, 1] |
//                     let col2 = subtract[col, 2] |

//                     validSubGridHelper[b, val, row, col, row1, row2, col1, col2]
//                 }
//             }
//         }
//     }
// }



// pred validSubGridHelper[b: Board, val: Number, row : Int, col: Int, row1: Int, row2: Int, col1: Int, col2: Int]{

//     no rowX : Int | {
//         // rowX != row
//         rowX = row1
        
//         validIndex[rowX]

//         b.board[rowX][col] = val
//         or
//         b.board[rowX][col1] = val
//         or
//         b.board[rowX][col2] = val
//     }

//     no rowY : Int | {
//         // rowY != row
//         rowY = row2
        
//         validIndex[rowY]

//         b.board[rowY][col] = val
//         or
//         b.board[rowY][col1] = val
//         or
//         b.board[rowY][col2] = val
//     }

//     no colX : Int | {
//         // colX != col
//         colX = col1
        
//         validIndex[colX]

//         b.board[row][colX] = val
//     }

//     no colY : Int | {
//         // colX != col
//         colY = col2
        
//         validIndex[colY]

//         b.board[row][colY] = val
//     }

//     // no val : Number | {
//     //     b.board[row][col] = val
//     //     and
//     //     (
//     //         b.board[row][col1] = val
//     //         or
//     //         b.board[row][col2] = val
//     //         or
//     //         b.board[row1][col] = val
//     //         or
//     //         b.board[row1][col1] = val
//     //         or
//     //         b.board[row1][col2] = val
//     //         or
//     //         b.board[row2][col] = val
//     //         or
//     //         b.board[row2][col1] = val
//     //         or
//     //         b.board[row2][col2] = val
//     //     )
//     // }
// }


