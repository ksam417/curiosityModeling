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

    example wellFormedPass is {wellformed[`testBoard]} for{

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

    example wellformedFail is { not wellformed[`invalidBoard]
    } for {

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
        `invalidBoard.board = (6, 0) -> 1
    }

    example wellformedFail2 is { not wellformed[`invalidBoard]
    } for {
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
    (0,0)->`ONE + (0,1)->`ONE + (0,2)->`ONE + (0,3)->`ONE + (0,4)->`ONE + (0,5)->`ONE + (0,6)->`ONE + (0,7)->`ONE + (0,8)->`ONE +
    (1,0)->`ONE + (1,1)->`ONE + (1,2)->`ONE + (1,3)->`ONE + (1,4)->`ONE + (1,5)->`ONE + (1,6)->`ONE + (1,7)->`ONE + (1,8)->`ONE +
    (2,0)->`ONE + (2,1)->`ONE + (2,2)->`ONE + (2,3)->`ONE + (2,4)->`ONE + (2,5)->`ONE + (2,6)->`ONE + (2,7)->`ONE + (2,8)->`ONE +
    (3,0)->`ONE + (3,1)->`ONE + (3,2)->`ONE + (3,3)->`ONE + (3,4)->`ONE + (3,5)->`ONE + (3,6)->`ONE + (3,7)->`ONE + (3,8)->`ONE +
    (4,0)->`ONE + (4,1)->`ONE + (4,2)->`ONE + (4,3)->`ONE + (4,4)->`ONE + (4,5)->`ONE + (4,6)->`ONE + (4,7)->`ONE + (4,8)->`ONE +
    (5,0)->`ONE + (5,1)->`ONE + (5,2)->`ONE + (5,3)->`ONE + (5,4)->`ONE + (5,5)->`ONE + (5,6)->`ONE + (5,7)->`ONE + (5,8)->`ONE +
    (6,0)->`ONE + (6,1)->`ONE + (6,2)->`ONE + (6,3)->`ONE + (6,4)->`ONE + (6,5)->`ONE + (6,6)->`ONE + (6,7)->`ONE + (6,8)->`ONE +
    (7,0)->`ONE + (7,1)->`ONE + (7,2)->`ONE + (7,3)->`ONE + (7,4)->`ONE + (7,5)->`ONE + (7,6)->`ONE + (7,7)->`ONE + (7,8)->`ONE +
    (8,0)->`ONE + (8,1)->`ONE + (8,2)->`ONE + (8,3)->`ONE + (8,4)->`ONE + (8,5)->`ONE + (8,6)->`ONE + (8,7)->`ONE + (8,8)->`ONE  
    }

    //Is an example of a full, and valid Sudoku board
    example fullBoardPass1 is {
        some testBoard: Board | fullBoard[testBoard]
    } for {
        Board = `testBoard
        Number = `ONE + `TWO + `THREE + `FOUR + `FIVE + `SIX + `SEVEN + `EIGHT + `NINE

        `testBoard.board =
      // Row 0
      (0,0)->`FIVE  + (0,1)->`THREE + (0,2)->`FOUR  + (0,3)->`SIX   + (0,4)->`SEVEN 
    + (0,5)->`EIGHT + (0,6)->`NINE  + (0,7)->`ONE   + (0,8)->`TWO +
      // Row 1
      (1,0)->`SIX   + (1,1)->`SEVEN + (1,2)->`TWO   + (1,3)->`ONE   + (1,4)->`NINE 
    + (1,5)->`FIVE  + (1,6)->`THREE + (1,7)->`FOUR  + (1,8)->`EIGHT +
      // Row 2
      (2,0)->`ONE   + (2,1)->`NINE  + (2,2)->`EIGHT + (2,3)->`THREE + (2,4)->`FOUR  
    + (2,5)->`TWO   + (2,6)->`FIVE  + (2,7)->`SIX   + (2,8)->`SEVEN +
      // Row 3
      (3,0)->`EIGHT + (3,1)->`FIVE  + (3,2)->`NINE  + (3,3)->`SEVEN + (3,4)->`SIX  
    + (3,5)->`ONE   + (3,6)->`FOUR  + (3,7)->`TWO   + (3,8)->`THREE +
      // Row 4
      (4,0)->`FOUR  + (4,1)->`TWO   + (4,2)->`SIX   + (4,3)->`EIGHT + (4,4)->`FIVE  
    + (4,5)->`THREE + (4,6)->`SEVEN + (4,7)->`NINE  + (4,8)->`ONE +
      // Row 5
      (5,0)->`SEVEN + (5,1)->`ONE   + (5,2)->`THREE + (5,3)->`NINE  + (5,4)->`TWO  
    + (5,5)->`FOUR  + (5,6)->`EIGHT + (5,7)->`FIVE  + (5,8)->`SIX +
      // Row 6
      (6,0)->`NINE  + (6,1)->`SIX   + (6,2)->`ONE   + (6,3)->`FIVE  + (6,4)->`THREE 
    + (6,5)->`SEVEN + (6,6)->`TWO   + (6,7)->`EIGHT + (6,8)->`FOUR +
      // Row 7
      (7,0)->`TWO   + (7,1)->`EIGHT + (7,2)->`SEVEN + (7,3)->`FOUR  + (7,4)->`ONE   
    + (7,5)->`NINE  + (7,6)->`SIX   + (7,7)->`THREE + (7,8)->`FIVE +
      // Row 8
      (8,0)->`THREE + (8,1)->`FOUR  + (8,2)->`FIVE  + (8,3)->`TWO   + (8,4)->`EIGHT 
    + (8,5)->`SIX   + (8,6)->`ONE   + (8,7)->`SEVEN + (8,8)->`NINE

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

  // Assign a value for every cell in all rows except row 4
  `testBoard.board =
    // Row 0
    (0,0)->`ONE + (0,1)->`ONE + (0,2)->`ONE + (0,3)->`ONE + (0,4)->`ONE + (0,5)->`ONE + (0,6)->`ONE + (0,7)->`ONE + (0,8)->`ONE +
    // Row 1
    (1,0)->`ONE + (1,1)->`ONE + (1,2)->`ONE + (1,3)->`ONE + (1,4)->`ONE + (1,5)->`ONE + (1,6)->`ONE + (1,7)->`ONE + (1,8)->`ONE +
    // Row 2
    (2,0)->`ONE + (2,1)->`ONE + (2,2)->`ONE + (2,3)->`ONE + (2,4)->`ONE + (2,5)->`ONE + (2,6)->`ONE + (2,7)->`ONE + (2,8)->`ONE +
    // Row 3
    (3,0)->`ONE + (3,1)->`ONE + (3,2)->`ONE + (3,3)->`ONE + (3,4)->`ONE + (3,5)->`ONE + (3,6)->`ONE + (3,7)->`ONE + (3,8)->`ONE +
    // Row 4 is intentionally omitted.
    // Row 5
    (5,0)->`ONE + (5,1)->`ONE + (5,2)->`ONE + (5,3)->`ONE + (5,4)->`ONE + (5,5)->`ONE + (5,6)->`ONE + (5,7)->`ONE + (5,8)->`ONE +
    // Row 6
    (6,0)->`ONE + (6,1)->`ONE + (6,2)->`ONE + (6,3)->`ONE + (6,4)->`ONE + (6,5)->`ONE + (6,6)->`ONE + (6,7)->`ONE + (6,8)->`ONE +
    // Row 7
    (7,0)->`ONE + (7,1)->`ONE + (7,2)->`ONE + (7,3)->`ONE + (7,4)->`ONE + (7,5)->`ONE + (7,6)->`ONE + (7,7)->`ONE + (7,8)->`ONE +
    // Row 8
    (8,0)->`ONE + (8,1)->`ONE + (8,2)->`ONE + (8,3)->`ONE + (8,4)->`ONE + (8,5)->`ONE + (8,6)->`ONE + (8,7)->`ONE + (8,8)->`ONE
}

// This test case should fail because it is missing column 7
example fullBoardFail_missingColumn is {
  some testBoard: Board | not fullBoard[testBoard]
} for {
  Board = `testBoard
  Number = `ONE + `TWO + `THREE + `FOUR + `FIVE + `SIX + `SEVEN + `EIGHT + `NINE

  // Assign a value for every cell for all rows (0..8) except column 7 is left out
  `testBoard.board =
    // Row 0
    (0,0)->`ONE + (0,1)->`ONE + (0,2)->`ONE + (0,3)->`ONE + (0,4)->`ONE + (0,5)->`ONE + (0,6)->`ONE + (0,8)->`ONE +
    // Row 1
    (1,0)->`ONE + (1,1)->`ONE + (1,2)->`ONE + (1,3)->`ONE + (1,4)->`ONE + (1,5)->`ONE + (1,6)->`ONE + (1,8)->`ONE +
    // Row 2
    (2,0)->`ONE + (2,1)->`ONE + (2,2)->`ONE + (2,3)->`ONE + (2,4)->`ONE + (2,5)->`ONE + (2,6)->`ONE + (2,8)->`ONE +
    // Row 3
    (3,0)->`ONE + (3,1)->`ONE + (3,2)->`ONE + (3,3)->`ONE + (3,4)->`ONE + (3,5)->`ONE + (3,6)->`ONE + (3,8)->`ONE +
    // Row 4
    (4,0)->`ONE + (4,1)->`ONE + (4,2)->`ONE + (4,3)->`ONE + (4,4)->`ONE + (4,5)->`ONE + (4,6)->`ONE + (4,8)->`ONE +
    // Row 5
    (5,0)->`ONE + (5,1)->`ONE + (5,2)->`ONE + (5,3)->`ONE + (5,4)->`ONE + (5,5)->`ONE + (5,6)->`ONE + (5,8)->`ONE +
    // Row 6
    (6,0)->`ONE + (6,1)->`ONE + (6,2)->`ONE + (6,3)->`ONE + (6,4)->`ONE + (6,5)->`ONE + (6,6)->`ONE + (6,8)->`ONE +
    // Row 7
    (7,0)->`ONE + (7,1)->`ONE + (7,2)->`ONE + (7,3)->`ONE + (7,4)->`ONE + (7,5)->`ONE + (7,6)->`ONE + (7,8)->`ONE +
    // Row 8
    (8,0)->`ONE + (8,1)->`ONE + (8,2)->`ONE + (8,3)->`ONE + (8,4)->`ONE + (8,5)->`ONE + (8,6)->`ONE + (8,8)->`ONE
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