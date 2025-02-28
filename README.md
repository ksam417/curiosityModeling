# curiosityModeling

1) Project Objective: What are you trying to model? Include a brief description that would give someone unfamiliar with the topic a basic understanding of your goal.

When we were going through the ideation process, we came up with a few options (BlackJack, Sudoku, and Uno). All of these were games that we had both played growing up, and we thought it would be cool to be under the hood with them. We modeled the classic logic puzzle where the objective is to fill a 9×9 grid so that each row, column, and 3×3 subgrid contains all the digits from 1 through 9 exactly once. We debated other ideas like Uno or Blackjack, but Sudoku offered a focused domain with clear constraints to verify. Through this model, we wanted to gain deeper insights into how constraint-solving and systematic search apply to puzzle-solving strategies.



2) Model Design and Visualization: Give an overview of your model design choices, what checks or run statements you wrote, and what we should expect to see from an instance produced by the Sterling visualizer. How should we look at and interpret an instance created by your spec? Did you create a custom visualization, or did you use the default?



3) Signatures and Predicates: At a high level, what do each of your sigs and preds represent in the context of the model? Justify the purpose for their existence and how they fit together.

Our first sig is a Boolean that we utilize to check for validity in the numbers passed into the board, later on. 

The next sig is the board, which we create as a partial function from (int, int) representing row and column, to an integer at that row and column value. 

After this, we dive into our predicates beginning with wellFormed, at a high level just ensures there are 9 rows and columns. 

Then we incorporate our validNumber sig into a validNumberSetup predicate that makes sure we have a mapping from number to boolean. 

The predicate validRow, defines what a valid row is in Sudoku. We check that for each row column pair, for a specific number, if the number is a valid number, and the cell at that row/col equals that number then that implies that every other row does not have the same number in that same cell. 

The predicate validCol, defines what a valid row is in Sudoku. We check that for each row column pair, for a specific number, if the number is a valid number, and the cell at that row/col equals that number then that implies that every other Col does not have the same number in that same cell. 

The predicate validSubGrid...

The predicate fullBoard...



4) Testing: What tests did you write to test your model itself? What tests did you write to verify properties about your domain area? Feel free to give a high-level overview of this.



5) Documentation: Make sure your model and test files are well-documented. This will help in understanding the structure and logic of your project.
