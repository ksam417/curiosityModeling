#lang forge/froglet

open "sudoku.frg"

// Define a predicate that creates a row and places values in it
pred firstRowOne {
  some b: Board | b.board[0][0] = `ONE 
             and b.board[0][1] = `ONE 
             and b.board[0][2] = `ONE
}

// Define a predicate that creates a column and places values in it
pred firstColumnOne {
  some b: Board | b.board[0][0] = `ONE 
             and b.board[1][0] = `ONE 
             and b.board[2][0] = `ONE
}

test suite for wellformed{
  

    // Test that the wellformed predicate works as expected

    example wellFormedPass is { some testBoard: Board | wellformed[testBoard]} for{

        // For row, col >= 9, we have no cells assigned.  
  // Rows and columns 0..8 can have any values or be empty; 
  // the key is that we don’t try to place anything out of 0..8 range.

        Board = `testBoard
        Number = `ONE + `TWO + `THREE + `FOUR + `FIVE + `SIX + `SEVEN + `EIGHT + `NINE

        ONE = `ONE
        TWO = `TWO
        THREE = `THREE
        FOUR = `FOUR
        FIVE = `FIVE
        SIX = `SIX
        SEVEN = `SEVEN
        EIGHT = `EIGHT
        NINE = `NINE

        `testBoard.board = (0,0) -> `ONE + (0,1) -> `TWO + (0,2) -> `THREE + (1,0) -> `FOUR + (1,1) -> `FIVE + (1,2) -> `SIX
    }

    example wellformedFail is { some invalidBoard: Board | not wellformed[invalidBoard]} for {

        Board = `invalidBoard
        Number = `ONE + `TWO + `THREE + `FOUR + `FIVE + `SIX + `SEVEN + `EIGHT + `NINE

        ONE = `ONE
        TWO = `TWO
        THREE = `THREE
        FOUR = `FOUR
        FIVE = `FIVE
        SIX = `SIX
        SEVEN = `SEVEN
        EIGHT = `EIGHT
        NINE = `NINE

        // Incorrectly place a cell at row 9
        `invalidBoard.board = (6, 0) -> `ONE
    }

    example wellformedFail2 is { some invalidBoard: Board | not wellformed[invalidBoard]} for {
        Board = `invalidBoard
        Number = `ONE + `TWO + `THREE + `FOUR + `FIVE + `SIX + `SEVEN + `EIGHT + `NINE

        ONE = `ONE
        TWO = `TWO
        THREE = `THREE
        FOUR = `FOUR
        FIVE = `FIVE
        SIX = `SIX
        SEVEN = `SEVEN
        EIGHT = `EIGHT
        NINE = `NINE

        // Incorrectly place a cell at row 0 and col 6
        `invalidBoard.board = (0, 6) -> `ONE
    }

    nonvacuous_wellformed: assert wellformed is sat

    // Assert that a board with a valid first row is consistent with being wellformed.
    nonvacuous_fullFirstRow: assert firstRowOne is consistent with wellformed for 1 Board

    // Assert that a board with a valid first column is consistent with being wellformed.
    nonvacuous_firstColumn: assert firstColumnOne is consistent with wellformed for 1 Board

}

pred firstRowTwo {
  some b: Board | 
      b.board[0][0] = `ONE and 
      b.board[0][1] = `TWO and 
      b.board[0][2] = `THREE
}

test suite for validRow {
    example validRowPass is {
    some testBoard: Board | validRow[testBoard]
  } for {

    Board = `testBoard
    Number = `ONE + `TWO + `THREE + `FOUR + `FIVE + `SIX + `SEVEN + `EIGHT + `NINE

    ONE = `ONE
    TWO = `TWO
    THREE = `THREE
    FOUR = `FOUR
    FIVE = `FIVE
    SIX = `SIX
    SEVEN = `SEVEN
    EIGHT = `EIGHT
    NINE = `NINE

    `testBoard.board =
      (0, -3) -> `ONE
    + (0, -2) -> `TWO
    + (0, -1) -> `THREE
    + (0, 0)  -> `FOUR
    + (0, 1)  -> `FIVE
    + (0, 2)  -> `SIX
    + (0, 3)  -> `SEVEN
    + (0, 4)  -> `EIGHT
    + (0, 5)  -> `NINE
  }

  example validRowPass2 is {
  some testBoard: Board | validRow[testBoard]
} for {
  Board = `testBoard
  Number = `ONE + `TWO + `THREE + `FOUR + `FIVE + `SIX + `SEVEN + `EIGHT + `NINE

  ONE    = `ONE
  TWO    = `TWO
  THREE  = `THREE
  FOUR   = `FOUR
  FIVE   = `FIVE
  SIX    = `SIX
  SEVEN  = `SEVEN
  EIGHT  = `EIGHT
  NINE   = `NINE

  -- Row 5 is assigned unique numbers for all 9 columns (from col -3 to 5)
  `testBoard.board =
       (5, -3) -> `ONE
     + (5, -2) -> `TWO
     + (5, -1) -> `THREE
     + (5,  0) -> `FOUR
     + (5,  1) -> `FIVE
     + (5,  2) -> `SIX
     + (5,  3) -> `SEVEN
     + (5,  4) -> `EIGHT
     + (5,  5) -> `NINE
}



    example validRowFail is {
    some testBoard: Board | not validRow[testBoard]
  } for {

    Board = `testBoard
    Number = `ONE + `TWO + `THREE + `FOUR + `FIVE + `SIX + `SEVEN + `EIGHT + `NINE

    ONE = `ONE
    TWO = `TWO
    THREE = `THREE
    FOUR = `FOUR
    FIVE = `FIVE
    SIX = `SIX
    SEVEN = `SEVEN
    EIGHT = `EIGHT
    NINE = `NINE

    -- Use the same row but duplicate ‘ONE’ to force a fail
    `testBoard.board =
      (0, -3) -> `ONE
    + (0, -2) -> `TWO
    + (0, -1) -> `THREE
    + (0, 0)  -> `FOUR
    + (0, 1)  -> `FIVE
    + (0, 2)  -> `SIX
    + (0, 3)  -> `SEVEN
    + (0, 4)  -> `EIGHT
    + (0, 5)  -> `ONE    -- Duplicate `ONE in the same row
  }

  example validRowFail2 is {
  some testBoard: Board | not validRow[testBoard]
} for {
  Board = `testBoard
  Number = `ONE + `TWO + `THREE + `FOUR + `FIVE + `SIX + `SEVEN + `EIGHT + `NINE

  ONE    = `ONE
  TWO    = `TWO
  THREE  = `THREE
  FOUR   = `FOUR
  FIVE   = `FIVE
  SIX    = `SIX
  SEVEN  = `SEVEN
  EIGHT  = `EIGHT
  NINE   = `NINE

  -- Row 5 has a duplicate: `ONE appears twice (in columns -3 and -2)
  `testBoard.board =
       (5, -3) -> `ONE
     + (5, -2) -> `ONE    -- Duplicate `ONE here
     + (5, -1) -> `THREE
     + (5,  0) -> `FOUR
     + (5,  1) -> `FIVE
     + (5,  2) -> `SIX
     + (5,  3) -> `SEVEN
     + (5,  4) -> `EIGHT
     + (5,  5) -> `NINE
}

// Assert that firstRow is consistent with validRow.
// (In other words, there is at least one board with a first row that can be arranged 
// to satisfy the validRow predicate.)
nonvacuous_firstRow: assert firstRowTwo is consistent with validRow for 1 Board

// Assert that validRow is satisfiable
nonvacuous_validRow: assert validRow is sat

}


pred firstColTwo {
  some b: Board |
      b.board[-3][0] = `ONE and
      b.board[-2][0] = `TWO and
      b.board[-1][0] = `THREE
}

test suite for validCol {

  // Test that the validCol predicate works as expected, where col 0 is completely full of unique values. 

    example validCol is {
        some testBoard: Board | validCol[testBoard]
    } for{

        Board = `testBoard
        Number = `ONE + `TWO + `THREE + `FOUR + `FIVE + `SIX + `SEVEN + `EIGHT + `NINE

        ONE = `ONE
        TWO = `TWO
        THREE = `THREE
        FOUR = `FOUR
        FIVE = `FIVE
        SIX = `SIX
        SEVEN = `SEVEN
        EIGHT = `EIGHT
        NINE = `NINE

        // Col 0 is valid
         `testBoard.board =
        ( -3, 0) -> `ONE
      + ( -2, 0) -> `TWO
      + ( -1, 0) -> `THREE
      + (  0, 0) -> `FOUR
      + (  1, 0) -> `FIVE
      + (  2, 0) -> `SIX
      + (  3, 0) -> `SEVEN
      + (  4, 0) -> `EIGHT
      + (  5, 0) -> `NINE
    }

    //This test case should pass because of the unique values being present throughout the column
    example validCol1 is {
        some testBoard: Board | validCol[testBoard]
    } for{

        Board = `testBoard
        Number = `ONE + `TWO + `THREE + `FOUR + `FIVE + `SIX + `SEVEN + `EIGHT + `NINE

        ONE = `ONE
        TWO = `TWO
        THREE = `THREE
        FOUR = `FOUR
        FIVE = `FIVE
        SIX = `SIX
        SEVEN = `SEVEN
        EIGHT = `EIGHT
        NINE = `NINE

        // Col -3 is valid
        `testBoard.board =
        (-3, -3) -> `ONE
        + (-2, -3) -> `TWO
        + (-1, -3) -> `THREE
        + (0,  -3) -> `FOUR
        + (1,  -3) -> `FIVE
        + (2,  -3) -> `SIX
        + (3,  -3) -> `SEVEN
        + (4,  -3) -> `EIGHT
        + (5,  -3) -> `NINE
    }

    //This test should pass because the column is valid, with unique values in each row
    example validCol2 is {
        some testBoard: Board | validCol[testBoard]
    } for{

        Board = `testBoard
        Number = `ONE + `TWO + `THREE + `FOUR + `FIVE + `SIX + `SEVEN + `EIGHT + `NINE

        ONE = `ONE
        TWO = `TWO
        THREE = `THREE
        FOUR = `FOUR
        FIVE = `FIVE
        SIX = `SIX
        SEVEN = `SEVEN
        EIGHT = `EIGHT
        NINE = `NINE

        // Column 5 is valid: assigned unique values to rows -3 through 5 in column 5
  `testBoard.board =
      (-3, 5) -> `ONE
    + (-2, 5) -> `TWO
    + (-1, 5) -> `THREE
    + ( 0, 5) -> `FOUR
    + ( 1, 5) -> `FIVE
    + ( 2, 5) -> `SIX
    + ( 3, 5) -> `SEVEN
    + ( 4, 5) -> `EIGHT
    + ( 5, 5) -> `NINE
    }

    //This test case should fail because the column has a duplicate value

    example validColFail is {
        some testBoard: Board | not validCol[testBoard]
    } for {
        
        Board = `testBoard
        Number = `ONE + `TWO + `THREE + `FOUR + `FIVE + `SIX + `SEVEN + `EIGHT + `NINE

        ONE = `ONE
        TWO = `TWO
        THREE = `THREE
        FOUR = `FOUR
        FIVE = `FIVE
        SIX = `SIX
        SEVEN = `SEVEN
        EIGHT = `EIGHT
        NINE = `NINE

        // Column 0 is invalid: duplicate value in the same column causes failure
  `testBoard.board =
      (-3, 0) -> `ONE
    + (-2, 0) -> `TWO
    + (-1, 0) -> `THREE
    + ( 0, 0) -> `FOUR
    + ( 1, 0) -> `FIVE
    + ( 2, 0) -> `SIX
    + ( 3, 0) -> `SEVEN
    + ( 4, 0) -> `EIGHT
    + ( 5, 0) -> `ONE  
    }

    //This test case should fail because the column is not valid

    example validColFail1 is {
        some testBoard: Board | not validCol[testBoard]
    } for {
        
        Board = `testBoard
        Number = `ONE + `TWO + `THREE + `FOUR + `FIVE + `SIX + `SEVEN + `EIGHT + `NINE

        ONE = `ONE
        TWO = `TWO
        THREE = `THREE
        FOUR = `FOUR
        FIVE = `FIVE
        SIX = `SIX
        SEVEN = `SEVEN
        EIGHT = `EIGHT
        NINE = `NINE

        // Col -3 is invalid due to a duplicate value 
    `testBoard.board =
        (-3, -3) -> `ONE
    + (-2, -3) -> `TWO
    + (-1, -3) -> `THREE
    + (0, -3)  -> `FOUR
    + (1, -3)  -> `FIVE
    + (2, -3)  -> `SIX
    + (3, -3)  -> `SEVEN
    + (4, -3)  -> `EIGHT
    + (5, -3)  -> `ONE
    }

     // Assert that firstColTwo is consistent with validCol.
  nonvacuous_firstCol: assert firstColTwo is consistent with validCol for 1 Board

  // Assert that validCol is satisfiable.
  nonvacuous_validCol: assert validCol is sat
}

test suite for fullBoard{

    //Filling a board completely should be a valid test case regardless of the values at each cell
    example fullBoardPass is {
        some testBoard: Board | fullBoard[testBoard]
    } for {
        Board = `testBoard
        Number = `ONE + `TWO + `THREE + `FOUR + `FIVE + `SIX + `SEVEN + `EIGHT + `NINE

        // Assign every cell in rows 0..8 and columns 0..8 the value `ONE.
  `testBoard.board =
    // Row -3
    (-3,-3)->`ONE + (-3,-2)->`ONE + (-3,-1)->`ONE + (-3, 0)->`ONE + (-3, 1)->`ONE + (-3, 2)->`ONE + (-3, 3)->`ONE + (-3, 4)->`ONE + (-3, 5)->`ONE +
    // Row -2 
    (-2,-3)->`ONE + (-2,-2)->`ONE + (-2,-1)->`ONE + (-2, 0)->`ONE + (-2, 1)->`ONE + (-2, 2)->`ONE + (-2, 3)->`ONE + (-2, 4)->`ONE + (-2, 5)->`ONE +
    // Row -1
    (-1,-3)->`ONE + (-1,-2)->`ONE + (-1,-1)->`ONE + (-1, 0)->`ONE + (-1, 1)->`ONE + (-1, 2)->`ONE + (-1, 3)->`ONE + (-1, 4)->`ONE + (-1, 5)->`ONE +
    // Row 0 
    (0,-3)->`ONE  + (0,-2)->`ONE  + (0,-1)->`ONE  + (0, 0)->`ONE  + (0, 1)->`ONE  + (0, 2)->`ONE  + (0, 3)->`ONE  + (0, 4)->`ONE  + (0, 5)->`ONE +
    // Row 1
    (1,-3)->`ONE  + (1,-2)->`ONE  + (1,-1)->`ONE  + (1, 0)->`ONE  + (1, 1)->`ONE  + (1, 2)->`ONE  + (1, 3)->`ONE  + (1, 4)->`ONE  + (1, 5)->`ONE +
    // Row 2 
    (2,-3)->`ONE  + (2,-2)->`ONE  + (2,-1)->`ONE  + (2, 0)->`ONE  + (2, 1)->`ONE  + (2, 2)->`ONE  + (2, 3)->`ONE  + (2, 4)->`ONE  + (2, 5)->`ONE +
    // Row 3 
    (3,-3)->`ONE  + (3,-2)->`ONE  + (3,-1)->`ONE  + (3, 0)->`ONE  + (3, 1)->`ONE  + (3, 2)->`ONE  + (3, 3)->`ONE  + (3, 4)->`ONE  + (3, 5)->`ONE +
    // Row 4 
    (4,-3)->`ONE  + (4,-2)->`ONE  + (4,-1)->`ONE  + (4, 0)->`ONE  + (4, 1)->`ONE  + (4, 2)->`ONE  + (4, 3)->`ONE  + (4, 4)->`ONE  + (4, 5)->`ONE +
    // Row 5 
    (5,-3)->`ONE  + (5,-2)->`ONE  + (5,-1)->`ONE  + (5, 0)->`ONE  + (5, 1)->`ONE  + (5, 2)->`ONE  + (5, 3)->`ONE  + (5, 4)->`ONE  + (5, 5)->`ONE 
    }

    //Is an example of a full, and valid Sudoku board
    example fullBoardPass1 is {
        some testBoard: Board | fullBoard[testBoard]
    } for {
        Board = `testBoard
        Number = `ONE + `TWO + `THREE + `FOUR + `FIVE + `SIX + `SEVEN + `EIGHT + `NINE

        `testBoard.board =
    // Row -3
    (-3,-3)->`FIVE  + (-3,-2)->`THREE + (-3,-1)->`FOUR  + (-3,0)->`SIX   + (-3,1)->`SEVEN 
  + (-3,2)->`EIGHT + (-3,3)->`NINE  + (-3,4)->`ONE   + (-3,5)->`TWO +
    // Row -2
    (-2,-3)->`SIX   + (-2,-2)->`SEVEN + (-2,-1)->`TWO   + (-2,0)->`ONE   + (-2,1)->`NINE 
  + (-2,2)->`FIVE  + (-2,3)->`THREE + (-2,4)->`FOUR  + (-2,5)->`EIGHT +
    // Row -1 
    (-1,-3)->`ONE   + (-1,-2)->`NINE  + (-1,-1)->`EIGHT + (-1,0)->`THREE + (-1,1)->`FOUR  
  + (-1,2)->`TWO   + (-1,3)->`FIVE  + (-1,4)->`SIX   + (-1,5)->`SEVEN +
    // Row 0
    (0,-3)->`EIGHT + (0,-2)->`FIVE  + (0,-1)->`NINE  + (0,0)->`SEVEN + (0,1)->`SIX  
  + (0,2)->`ONE   + (0,3)->`FOUR  + (0,4)->`TWO   + (0,5)->`THREE +
    // Row 1
    (1,-3)->`FOUR  + (1,-2)->`TWO   + (1,-1)->`SIX   + (1,0)->`EIGHT + (1,1)->`FIVE  
  + (1,2)->`THREE + (1,3)->`SEVEN + (1,4)->`NINE  + (1,5)->`ONE +
    // Row 2 
    (2,-3)->`SEVEN + (2,-2)->`ONE   + (2,-1)->`THREE + (2,0)->`NINE  + (2,1)->`TWO  
  + (2,2)->`FOUR  + (2,3)->`EIGHT + (2,4)->`FIVE  + (2,5)->`SIX +
    // Row 3
    (3,-3)->`NINE  + (3,-2)->`SIX   + (3,-1)->`ONE   + (3,0)->`FIVE  + (3,1)->`THREE 
  + (3,2)->`SEVEN + (3,3)->`TWO   + (3,4)->`EIGHT + (3,5)->`FOUR +
    // Row 4 
    (4,-3)->`TWO   + (4,-2)->`EIGHT + (4,-1)->`SEVEN + (4,0)->`FOUR  + (4,1)->`ONE   
  + (4,2)->`NINE  + (4,3)->`SIX   + (4,4)->`THREE + (4,5)->`FIVE +
    // Row 5 
    (5,-3)->`THREE + (5,-2)->`FOUR  + (5,-1)->`FIVE  + (5,0)->`TWO   + (5,1)->`EIGHT 
  + (5,2)->`SIX   + (5,3)->`ONE   + (5,4)->`SEVEN + (5,5)->`NINE

    }

    //Is  an example of an invalid full Sudoku board, the board is not a 9 x 9 grid

    example fullBoardFail is {
        some testBoard: Board | not fullBoard[testBoard]
    } for {
        Board = `testBoard
        Number = `ONE + `TWO + `THREE + `FOUR + `FIVE + `SIX + `SEVEN + `EIGHT + `NINE

        `testBoard.board =
        (0, 0) -> `ONE
        + (0, 1) -> `TWO
        + (0, 2) -> `THREE
        + (1, 0) -> `FOUR
        + (1, 1) -> `FIVE
        + (1, 2) -> `SIX
        + (2, 0) -> `SEVEN
        + (2, 1) -> `EIGHT
    }

  
  // This example highlights that missing row 4 should result in a failed test case
  example fullBoardFail_missingRow is {
  some testBoard: Board | not fullBoard[testBoard]
} for {
  Board = `testBoard
  Number = `ONE + `TWO + `THREE + `FOUR + `FIVE + `SIX + `SEVEN + `EIGHT + `NINE

  // Assign a value for every cell in all rows except the omitted row (new row 1)
`testBoard.board =
    // Row -3 
    (-3,-3)->`ONE + (-3,-2)->`ONE + (-3,-1)->`ONE + (-3, 0)->`ONE + (-3, 1)->`ONE + (-3, 2)->`ONE + (-3, 3)->`ONE + (-3, 4)->`ONE + (-3, 5)->`ONE +
    // Row -2 
    (-2,-3)->`ONE + (-2,-2)->`ONE + (-2,-1)->`ONE + (-2, 0)->`ONE + (-2, 1)->`ONE + (-2, 2)->`ONE + (-2, 3)->`ONE + (-2, 4)->`ONE + (-2, 5)->`ONE +
    // Row -1 
    (-1,-3)->`ONE + (-1,-2)->`ONE + (-1,-1)->`ONE + (-1, 0)->`ONE + (-1, 1)->`ONE + (-1, 2)->`ONE + (-1, 3)->`ONE + (-1, 4)->`ONE + (-1, 5)->`ONE +
    // Row 0 
    (0,-3)->`ONE  + (0,-2)->`ONE  + (0,-1)->`ONE  + (0, 0)->`ONE  + (0, 1)->`ONE  + (0, 2)->`ONE  + (0, 3)->`ONE  + (0, 4)->`ONE  + (0, 5)->`ONE +
    // Row 1 is omitted 
    // Row 2
    (2,-3)->`ONE  + (2,-2)->`ONE  + (2,-1)->`ONE  + (2, 0)->`ONE  + (2, 1)->`ONE  + (2, 2)->`ONE  + (2, 3)->`ONE  + (2, 4)->`ONE  + (2, 5)->`ONE +
    // Row 3
    (3,-3)->`ONE  + (3,-2)->`ONE  + (3,-1)->`ONE  + (3, 0)->`ONE  + (3, 1)->`ONE  + (3, 2)->`ONE  + (3, 3)->`ONE  + (3, 4)->`ONE  + (3, 5)->`ONE +
    // Row 4
    (4,-3)->`ONE  + (4,-2)->`ONE  + (4,-1)->`ONE  + (4, 0)->`ONE  + (4, 1)->`ONE  + (4, 2)->`ONE  + (4, 3)->`ONE  + (4, 4)->`ONE  + (4, 5)->`ONE +
    // Row 5
    (5,-3)->`ONE  + (5,-2)->`ONE  + (5,-1)->`ONE  + (5, 0)->`ONE  + (5, 1)->`ONE  + (5, 2)->`ONE  + (5, 3)->`ONE  + (5, 4)->`ONE  + (5, 5)->`ONE
}

// This test case should fail because it is missing column 7
example fullBoardFail_missingColumn is {
  some testBoard: Board | not fullBoard[testBoard]
} for {
  Board = `testBoard
  Number = `ONE + `TWO + `THREE + `FOUR + `FIVE + `SIX + `SEVEN + `EIGHT + `NINE

  // Assign a value for every cell for all rows (0..8) except column 7 is left out
  `testBoard.board =
    // Row -3 
    (-3,-3)->`ONE + (-3,-2)->`ONE + (-3,-1)->`ONE + (-3, 0)->`ONE + (-3, 1)->`ONE + (-3, 2)->`ONE + (-3, 3)->`ONE + (-3, 5)->`ONE +
    // Row -2 
    (-2,-3)->`ONE + (-2,-2)->`ONE + (-2,-1)->`ONE + (-2, 0)->`ONE + (-2, 1)->`ONE + (-2, 2)->`ONE + (-2, 3)->`ONE + (-2, 5)->`ONE +
    // Row -1 
    (-1,-3)->`ONE + (-1,-2)->`ONE + (-1,-1)->`ONE + (-1, 0)->`ONE + (-1, 1)->`ONE + (-1, 2)->`ONE + (-1, 3)->`ONE + (-1, 5)->`ONE +
    // Row 0 
    (0,-3)->`ONE  + (0,-2)->`ONE  + (0,-1)->`ONE  + (0, 0)->`ONE  + (0, 1)->`ONE  + (0, 2)->`ONE  + (0, 3)->`ONE  + (0, 5)->`ONE +
    // Row 1 
    (1,-3)->`ONE  + (1,-2)->`ONE  + (1,-1)->`ONE  + (1, 0)->`ONE  + (1, 1)->`ONE  + (1, 2)->`ONE  + (1, 3)->`ONE  + (1, 5)->`ONE +
    // Row 2 
    (2,-3)->`ONE  + (2,-2)->`ONE  + (2,-1)->`ONE  + (2, 0)->`ONE  + (2, 1)->`ONE  + (2, 2)->`ONE  + (2, 3)->`ONE  + (2, 5)->`ONE +
    // Row 3
    (3,-3)->`ONE  + (3,-2)->`ONE  + (3,-1)->`ONE  + (3, 0)->`ONE  + (3, 1)->`ONE  + (3, 2)->`ONE  + (3, 3)->`ONE  + (3, 5)->`ONE +
    // Row 4
    (4,-3)->`ONE  + (4,-2)->`ONE  + (4,-1)->`ONE  + (4, 0)->`ONE  + (4, 1)->`ONE  + (4, 2)->`ONE  + (4, 3)->`ONE  + (4, 5)->`ONE +
    // Row 5
    (5,-3)->`ONE  + (5,-2)->`ONE  + (5,-1)->`ONE  + (5, 0)->`ONE  + (5, 1)->`ONE  + (5, 2)->`ONE  + (5, 3)->`ONE  + (5, 5)->`ONE
}

}

test suite for validSubGrids{

    example subGridPass is {
        some testBoard: Board | validSubGrids[testBoard]
    } for {
        Board = `testBoard
        Number = `ONE + `TWO + `THREE + `FOUR + `FIVE + `SIX + `SEVEN + `EIGHT + `NINE

        `testBoard.board =
        (-3, -3) -> `ONE
        + (-3, -2) -> `TWO
        + (-3, -1) -> `THREE
        + (-2, -3) -> `FOUR
        + (-2, -2) -> `FIVE
        + (-2, -1) -> `SIX
        + (-1, -3) -> `SEVEN
        + (-1, -2) -> `EIGHT
        + (-1, -1) -> `NINE

    }

    example subGridPass1 is {
        some testBoard: Board | validSubGrids[testBoard]
    } for {
        Board = `testBoard
        Number = `ONE + `TWO + `THREE + `FOUR + `FIVE + `SIX + `SEVEN + `EIGHT + `NINE

        `testBoard.board =
        (3, 3) -> `ONE
        + (3, 4) -> `TWO
        + (3, 5) -> `THREE
        + (4, 3) -> `NINE 
        + (4, 4) -> `FOUR
        + (4, 5) -> `FIVE
        + (5, 3) -> `SIX
        + (5, 4) -> `SEVEN
        + (5, 5) -> `EIGHT

    }

    example subGridFail is {
        some testBoard: Board | not validSubGrids[testBoard]
    } for {

        Board = `testBoard
        Number = `ONE + `TWO + `THREE + `FOUR + `FIVE + `SIX + `SEVEN + `EIGHT + `NINE

        `testBoard.board =
    
        (-3, -3) -> `ONE
        + (-3, -2) -> `TWO
        + (-3, -1) -> `THREE
        + (-2, -3) -> `ONE
        + (-2, -2) -> `FOUR
        + (-2, -1) -> `FIVE
        + (-1, -3) -> `SIX
        + (-1, -2) -> `SEVEN
        + (-1, -1) -> `EIGHT
    }

    example subGridFail1 is {
        some testBoard: Board | not validSubGrids[testBoard]
    } for {

        Board = `testBoard
        Number = `ONE + `TWO + `THREE + `FOUR + `FIVE + `SIX + `SEVEN + `EIGHT + `NINE

            `testBoard.board =
        (0, 0) -> `ONE
        + (0, 1) -> `TWO
        + (0, 2) -> `THREE
        + (1, 0) -> `FOUR
        + (1, 1) -> `ONE    -- Duplicate `ONE
        + (1, 2) -> `FIVE
        + (2, 0) -> `SIX
        + (2, 1) -> `SEVEN
        + (2, 2) -> `EIGHT
    }
}