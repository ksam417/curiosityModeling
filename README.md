# curiosityModeling

1) Project Objective: What are you trying to model? Include a brief description that would give someone unfamiliar with the topic a basic understanding of your goal.

When we were going through the ideation process, we came up with a few options (BlackJack, Sudoku, and Uno). All of these were games that we had both played growing up, and we thought it would be cool to be under the hood with them. We modeled the classic logic puzzle where the objective is to fill a 9×9 grid so that each row, column, and 3×3 subgrid contains all the digits from 1 through 9 exactly once. We debated other ideas like Uno or Blackjack, but Sudoku offered a focused domain with clear constraints to verify. Through this model, we wanted to gain deeper insights into how constraint-solving and systematic search apply to puzzle-solving strategies.



2) Model Design and Visualization: Give an overview of your model design choices, what checks or run statements you wrote, and what we should expect to see from an instance produced by the Sterling visualizer. How should we look at and interpret an instance created by your spec? Did you create a custom visualization, or did you use the default?

We utilized the default visualization.

3) Signatures and Predicates: At a high level, what do each of your sigs and preds represent in the context of the model? Justify the purpose for their existence and how they fit together.

Our first sig is a Boolean that we utilize to check for validity in the numbers passed into the board, later on.

The next sig is the board, which we create as a partial function from (int, int) representing row and column, to an integer at that row and column value.

After this, we dive into our predicates beginning with wellFormed, at a high level just ensures there are 9 rows and columns.

Then we incorporate our validNumber sig into a validNumberSetup predicate that makes sure we have a mapping from number to boolean.

The predicate validCol, defines what a valid row is in Sudoku. We check that for each row column pair, for a specific number, if the number is a valid number, and the cell at that row/col equals that number then that implies that every other Col does not have the same number in that same cell.

The predicate validRow, defines what a valid row is in Sudoku. We check that for each row column pair, for a specific number, if the number is a valid number, and the cell at that row/col equals that number then that implies that every other row does not have the same number in that same cell.

The predicate fullBoard defines what it means for a sudoku board to be full, simply based on row and column numbers. There should be 9 rows and 9 columns, where there is a value at each of the cells.



4) Testing: What tests did you write to test your model itself? What tests did you write to verify properties about your domain area? Feel free to give a high-level overview of this.

The main things that we tested was the functionality for all of the predicates that involved structurally setting up the game. We included passing and failing tests, to clearly demonstrate edge cases that should be accounted for by our functionality. We also included a variety of assert tests to further ensure that our major predicates are satisfactory, align with wellformedness, and overall function as intended.



5) Documentation: Make sure your model and test files are well-documented. This will help in understanding the structure and logic of your project.
