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
        (row < 0 or row > 9 or col < 0 or col > 9)
        implies no b.board[row][col]
    }
}

// Setting up the valid number sig
pred validNumberSetup[v: validNumber]{
    // Makes sure that we have a mapping from number to boolean 
    // as we make it so that numbers between -1 and 10 (0-9) map 
    // to true and other numbers map to false 
    all num : Int | {
        (num > -1 or num < 10) implies {
            v.valid[num] = True
        }

        (num < 0 or num > 9) implies {
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
    all row, num, col : Int |{
        // if the number is valid (0-9) and the cell equals that number..
        (v.valid[num] = True and b.board[row][col] = num) implies{
            // every other row that isn't our original row, does not have the same number in that same column/cell
            all otherRow : Int | otherRow != row {
                b.board[otherRow][col] != num
            }
        }
    }
}

// Predicate defining what a valid row is ini Sudoku
pred validCol[v: validNumber, b: Board] {
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