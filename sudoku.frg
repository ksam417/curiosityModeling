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
    // Making sure that our board is a 9x9 size 
    all row, col: Int | {
        (row < -3 or row > 5 or col < -3 or col > 5) implies {
            no b.board[row][col]
        }
    }
}

// Predicate defining what a valid col is in Sudoku
pred validCol[b: Board] {
    // For all row and col integer pairings...
    all row, col : Int |{
        // if the row and col pair is valid (in the board) then...
        (row >= -3 and row <= 5 and col >= -3 and col <= 5) implies {
            // there is some value in the board such that...
            some val : Number | {
                // the board is equal to that value
                b.board[row][col] = val
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
            // there is some value in the board such that...
            some val : Number | {
                // the board is equal to that value
                b.board[row][col] = val
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

pred validSubGrids[b: Board]{
    all row, col : Int | {
        (row >= -3 and row <= 5 and col >= -3 and col <= 5) implies {
            some val : Number | {
                b.board[row][col] = val



                let rowMod = abs[remainder[row, 3]] |
                let colMod = abs[remainder[col, 3]] |

                (sign[row] > 1 and sign[col] > 1) implies {
                    // row top position and col top position
                    (rowMod = 0 and colMod = 0) implies {
                        let row1 = add[row, 1] |
                        let row2 = add[row, 2] |

                        let col1 = add[col, 1] |
                        let col2 = add[col, 2] |

                        validSubGridHelper[b, val, row, col, row1, row2, col1, col2]
                    } 

                    or

                    // row top position and col mid position
                    (rowMod = 0 and colMod = 1) implies {
                        let row1 = add[row, 1] |
                        let row2 = add[row, 2] |

                        let col1 = subtract[col, 1] |
                        let col2 = add[col, 1] |

                        validSubGridHelper[b, val, row, col, row1, row2, col1, col2]
                    }

                    or 

                    // row top position and col bottom position
                    (rowMod = 0 and colMod = 2) implies {
                        let row1 = add[row, 1] |
                        let row2 = add[row, 2] |

                        let col1 = subtract[col, 1] |
                        let col2 = subtract[col, 2] |

                        validSubGridHelper[b, val, row, col, row1, row2, col1, col2]
                    }

                    or 

                    // row mid position and col top position
                    (rowMod = 1 and colMod = 0) implies {
                        let row1 = subtract[row, 1] |
                        let row2 = add[row, 1] |

                        let col1 = add[col, 1] |
                        let col2 = add[col, 2] |

                        validSubGridHelper[b, val, row, col, row1, row2, col1, col2]
                    }

                    or 

                    // row mid position and col mid position
                    (rowMod = 1 and colMod = 1) implies {
                        let row1 = subtract[row, 1] |
                        let row2 = add[row, 1] |

                        let col1 = subtract[col, 1] |
                        let col2 = add[col, 1] |
                
                        validSubGridHelper[b, val, row, col, row1, row2, col1, col2]
                    }
                    
                    or 

                    // row mid position and col bottom position
                    (rowMod = 1 and colMod = 2) implies {
                        let row1 = subtract[row, 1] |
                        let row2 = add[row, 1] |

                        let col1 = subtract[col, 1] |
                        let col2 = subtract[col, 2] |

                        validSubGridHelper[b, val, row, col, row1, row2, col1, col2]
                    }

                    or 

                    // row bottom position and col top position
                    (rowMod = 2 and colMod = 0) implies {
                        let row1 = subtract[row, 1] |
                        let row2 = subtract[row, 2] |

                        let col1 = add[col, 1] |
                        let col2 = add[col, 2] |

                        validSubGridHelper[b, val, row, col, row1, row2, col1, col2]
                    }

                    or 

                    // row bottom position and col mid position
                    (rowMod = 2 and colMod = 1) implies {
                        let row1 = subtract[row, 1] |
                        let row2 = subtract[row, 2] |

                        let col1 = subtract[col, 1] |
                        let col2 = add[col, 1] |

                        validSubGridHelper[b, val, row, col, row1, row2, col1, col2]
                    }

                    or 

                    // row bottom position and col bottom position
                    (rowMod = 2 and colMod = 2) implies {
                        let row1 = subtract[row, 1] |
                        let row2 = subtract[row, 2] |

                        let col1 = subtract[col, 1] |
                        let col2 = subtract[col, 2] |

                        validSubGridHelper[b, val, row, col, row1, row2, col1, col2]
                    }
                }

                
            }
        }
    }
}

pred validSubGridHelper[b: Board, val: Number, row : Int, col: Int, row1: Int, row2: Int, col1: Int, col2: Int]{
    b.board[row][col1] != val
    b.board[row][col2] != val

    b.board[row1][col] != val
    b.board[row1][col1] != val
    b.board[row1][col2] != val

    b.board[row2][col] != val
    b.board[row2][col1] != val
    b.board[row2][col2] != val
}

run{
    some b : Board | {
        wellformed[b]
        fullBoard[b]
        validRow[b]
        validCol[b]
        validSubGrids[b]
    }
} for exactly 1 Board