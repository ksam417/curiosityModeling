#lang forge/froglet 

abstract sig Boolean {}
one sig True, False extends Boolean {}

// This is the definition of the sudoku board sig
sig Board {
    // Partial function from (Int,Int) to Int to get the integer on the board at some row and col 
    board: pfunc Int -> Int -> Int
}

one sig validNumber {
    valid : pfunc Int -> Boolean
}

// Predicate defining wellformedness of a Sudoku board 
pred wellformed[b: Board] {
    // Making sure that our board is a 9x9 size 
    all row, col: Int | {
        (row < 0 or row > 8 or col < 0 or col > 8) implies no b.board[row][col]
    }
}

// Setting up the valid number sig
pred validNumberSetup[v: validNumber]{
    // Makes sure that we have a mapping from number to boolean 
    // as we make it so that numbers between -1 and 10 (0-9) map 
    // to true and other numbers map to false 
    all num : Int | {
        (num > 0 and num < 10) implies {
            v.valid[num] = True
        }

        (num < 1 or num > 9) implies {
            v.valid[num] = False
        }
    }
}

// Predicate defining the starting state of a Sudoku board 
pred starting[b: Board] {
    // Saying that the board is empty upon start 
    all row, col: Int | {
        no b.board[row][col]
    }
}

// Predicate defining what a valid row is ini Sudoku
pred validRow[v: validNumber, b: Board] {
    // Check that for each row and col pair as well as possible number...
    all row, col, val : Int |{
        // if the number is valid (0-9) and the cell equals that number..
        (v.valid[val] = True and b.board[row][col] = val) implies{
            // every other row that isn't our original row, does not have the same number in that same column/cell
            all otherRow : Int | otherRow != row {
                b.board[otherRow][col] != val
            }
        }
    }
}

// Predicate defining what a valid row is in Sudoku
pred validCol[v: validNumber, b: Board]{
    // Check that for each row and col pair as well as possible number...
    all row, num, col : Int |{
        // if the number is valid (0-9) and the cell equals that number...
        (v.valid[num] = True and b.board[row][col] = num) implies{
            // every other col that isn't our original row, does not have the same number in that same row/cell 
            all otherCol: Int | otherRow != row {
                b.board[row][otherCol] != num
            }
        }
    }
}

pred validSubGrid[v: validNumber, b: Board]{
    all row, num, col : Int |{
        (v.valid[num] = True and b.board[row][col] = num) implies {
            let rowMod = remainder[row, 3]
            let colMod = remainder[col, 3]

            // row top position and col top position
            (rowMod = 0 and colMod = 0) implies {

            }

            // row top position and col mid position
            (rowMod = 0 and colMod = 1) implies {

            }

            // row top position and col bottom position
            (rowMod = 0 and colMod = 2) implies {

            }

            // row mid position and col top position
            (rowMod = 1 and colMod = 0) implies {

            }

            // row mid position and col mid position
            (rowMod = 1 and colMod = 1) implies {

            }
            
            // row mid position and col bottom position
            (rowMod = 1 and colMod = 2) implies {

            }

            // row bottom position and col top position
            (rowMod = 2 and colMod = 0) implies {

            }

            // row bottom position and col mid position
            (rowMod = 2 and colMod = 1) implies {

            }

            // row bottom position and col bottom position
            (rowMod = 2 and colMod = 2) implies {

            }

        }
    }
}

pred fullBoard[v: validNumber, b: Board]{
    all row, col: Int |{
        some num : Int |{
            v.valid[num] = True 
            b.board[row][col] = num
        }
    }
}