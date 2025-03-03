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
        (row < -3 or row > 5 or col < -3 or col > 5) implies {
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
        (row >= -3 and row <= 5 and col >= -3 and col <= 5) implies {
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
        (row >= -3 and row <= 5 and col >= -3 and col <= 5) implies {
            // there is some value in the board in the cell such that...
            let val = b.board[row][col] |

            (val != none) implies {
                // and there is not other row that is...
                no otherRow : Int | {
                    (otherRow >= -3 and otherRow <= 5)  
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
        (row >= -3 and row <= 5 and col >= -3 and col <= 5) implies {

            // there is some value in the board in the cell such that...
            let val = b.board[row][col] |

            (val != none) implies {
                // and there is not other col that is...
                no otherCol : Int | {
                    // valid, not equal to our current col, and has the same value as our current row + col pair
                    (otherCol >= -3 and otherCol <= 5)  
                    otherCol != col 
                    b.board[row][otherCol] = val    
                }
            }
        }
    }
}


// Predicate defining what it means to have valid subgrids across the board 
pred validSubGrids[b: Board]{
    // Looping over all of our possible row and col pairs, in which we hard check each subgrid range 
    // and use our helper in order to check that there are no duplicate numbers in the sub grids 
    all row, col : Int {
        // Top left subgrid
        (row >= -3 and row <= -1 and col >= -3 and col <= -1) implies {
            validSubGridsHelper[b, -3, -3]
        }
        
        or 

        // Top middle subgrid
        (row >= -3 and row <= -1 and col > -1 and col <= 2) implies {
            validSubGridsHelper[b, -3, 0]
        }
        
        or 

        // Top right subgrid
        (row >= -3 and row <= -1 and col > 2 and col <= 5) implies {
            validSubGridsHelper[b, -3, 3]

        }
        
        or 

        // Mid left subgrid
        (row > -1 and row <= 2 and col >= -3 and col <= -1) implies {
            validSubGridsHelper[b, 0, -3]
        }
        
        or 

        // Mid middle subgrid
        (row > -1 and row <= 2 and col > -1 and col <= 2) implies {
            validSubGridsHelper[b, 0, 0]
        }
        
        or 


        // Mid right subgrid
        (row > -1 and row <= 2 and col > 2 and col <= 5) implies {
            validSubGridsHelper[b, 0, 3]
        }
        
        or 

        // Bottom left subgrid
        (row > 2 and row <= 5 and col >= -3 and col <= -1) implies {
            validSubGridsHelper[b, 3, -3]
        }
        
        or 

        // Bottom middle subgrid
        (row > 2 and row <= 5 and col > -1 and col <= 5) implies {
            validSubGridsHelper[b, 3, 0]
        }
        
        or 

        // Mid right subgrid
        (row > 2 and row <= 5 and col > 2 and col <= 5) implies {
            validSubGridsHelper[b, 3, 3]
        }
    }
}

// Predicate defining the helper for the valid sub grid predicate 
pred validSubGridsHelper[b: Board, rowRef : Int, colRef :Int]{
    // There is no number in which there are duplicate values across all the 
    // different cells in the subgrid 
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

// Run statemnet checking all insatnces of winning boards in sudoku
run{
    // Running for some board where it abides by all of our rules 
    some b : Board | {
        wellformed[b]
        fullBoard[b]
        validRow[b]
        validCol[b]
        validSubGrids[b]
    }
} for exactly 1 Board

// Sig for Sudoku game where we have a begining board and a function
// connecting states of the board 
one sig SudokuGame {
    firstBoard: one Board,
    nextBoard: pfunc Board -> Board
}

// Predicate for what it means to place a number on the sudoku board 
pred placeNumber[prev: Board, r : Int, c: Int, post: Board] {

    // Make sure there is nothing at the spot in which the number is going to be placed
    no prev.board[r][c]


    // Ensure that we are placing the number at a valid cell on the board
    (r >= -3 and r <= 5 and c >= -3 and c <= 5)

    // Place some number on the board at the row and col pairing 
    some val : Number | {
        post.board[r][c] = val
    }

    // Ensure that when we place the number, it follows the valid row, col, and sub grid rules 
    validRow[post]
    validCol[post]
    validSubGrids[post]
    
    // Double check that all the elements in the two boards (before and after number placement) are 
    // the same besdies the new number we placed 
    all r2, c2: Int | {
        (r2 != r or c2 != c) implies {
            post.board[r2][c2] = prev.board[r2][c2]
        }
    }
}

// Predicate defining what game trace is 
pred gameTrace {
    // Make sure the that our first board in the trace is both empty and well formed
    wellformed[SudokuGame.firstBoard] 
    empty[SudokuGame.firstBoard]

    // For all boards we make it so that ...
    all b: Board | {
        // if this board has a next board in the game ...
        some SudokuGame.nextBoard[b] implies {
            // we choose some row and col to place our next number in the game 
            some row, col: Int| {
                placeNumber[b, row, col, SudokuGame.nextBoard[b]]
            }
        }

    }
}

// Run statement for the game trace where we run for 20 different Board states 
// and makes sure that our function connceting board states is linear 
showAGame: run {
    gameTrace
} for 20 Board for {nextBoard is linear}


/**
Below is our original approach for the subgrid validity. The approach was based on using the to 
take the mod/remainder of each row and column to know where we are in the subgrid and use that to 
check all of the other 8 cells within the subgrid. This approach was supposed to be with a grid 
that was 9x9 with only postive indices from 0-8 in which this approach would work and not with 
negative indicies.
**/

// pred validSubGrids[b: Board]{
//     all row, col : Int | {
//         (row >= -3 and row <= 5 and col >= -3 and col <= 5) implies {
//             let val = b.board[row][col] |
//             (val != none) implies {
//                 let rowMod = remainder[row, 3] |
//                 let colMod = remainder[col, 3] |

//                 (rowMod = -3 and colMod = -3) implies {
//                     let row1 = add[row, 1] |
//                     let row2 = add[row, 2] |

//                     let col1 = add[col, 1] |
//                     let col2 = add[col, 2] |

//                     validSubGridHelper[b, val, row, col, row1, row2, col1, col2]
//                 } 

//                 or

//                 // row top position and col mid position
//                 (rowMod = -3 and colMod = 1) implies {
//                     let row1 = add[row, 1] |
//                     let row2 = add[row, 2] |

//                     let col1 = subtract[col, 1] |
//                     let col2 = add[col, 1] |

//                     validSubGridHelper[b, val, row, col, row1, row2, col1, col2]
//                 }

//                 or 

//                 // row top position and col bottom position
//                 (rowMod = -3 and colMod = 2) implies {
//                     let row1 = add[row, 1] |
//                     let row2 = add[row, 2] |

//                     let col1 = subtract[col, 1] |
//                     let col2 = subtract[col, 2] |

//                     validSubGridHelper[b, val, row, col, row1, row2, col1, col2]
//                 }

//                 or 

//                 // row mid position and col top position
//                 (rowMod = 1 and colMod = -3) implies {
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
//                 (rowMod = 2 and colMod = -3) implies {
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


