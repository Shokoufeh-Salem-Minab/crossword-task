import sys

from math import inf
from crossword import *
from copy import deepcopy

BACKTRACK_COUNTER = 0
WORDS_TESTED = 0

class CrosswordCreator():

    def __init__(self, crossword):
        """
        Create new CSP crossword generate.
        """
        self.crossword = crossword
        self.domains = {
            var: self.crossword.words.copy()
            for var in self.crossword.variables
        }

    def letter_grid(self, assignment):
        """
        Return 2D array representing a given assignment.
        """
        letters = [
            [None for _ in range(self.crossword.width)]
            for _ in range(self.crossword.height)
        ]
        for variable, word in assignment.items():
            direction = variable.direction
            for k in range(len(word)):
                i = variable.i + (k if direction == Variable.DOWN else 0)
                j = variable.j + (k if direction == Variable.ACROSS else 0)
                letters[i][j] = word[k]
        return letters

    def print(self, assignment):
        """
        Print crossword assignment to the terminal.
        """
        letters = self.letter_grid(assignment)
        for i in range(self.crossword.height):
            for j in range(self.crossword.width):
                if self.crossword.structure[i][j]:
                    print(letters[i][j] or " ", end="")
                else:
                    print("█", end="")
            print()

    def save(self, assignment, filename):
        """
        Save crossword assignment to an image file.
        """
        from PIL import Image, ImageDraw, ImageFont
        cell_size = 100
        cell_border = 2
        interior_size = cell_size - 2 * cell_border
        letters = self.letter_grid(assignment)

        # Create a blank canvas
        img = Image.new(
            "RGBA",
            (self.crossword.width * cell_size,
             self.crossword.height * cell_size),
            "black"
        )
        font = ImageFont.truetype("assets/fonts/OpenSans-Regular.ttf", 80)
        draw = ImageDraw.Draw(img)

        for i in range(self.crossword.height):
            for j in range(self.crossword.width):

                rect = [
                    (j * cell_size + cell_border,
                     i * cell_size + cell_border),
                    ((j + 1) * cell_size - cell_border,
                     (i + 1) * cell_size - cell_border)
                ]
                if self.crossword.structure[i][j]:
                    draw.rectangle(rect, fill="white")
                    if letters[i][j]:
                        w, h = draw.textsize(letters[i][j], font=font)
                        draw.text(
                            (rect[0][0] + ((interior_size - w) / 2),
                             rect[0][1] + ((interior_size - h) / 2) - 10),
                            letters[i][j], fill="black", font=font
                        )

        img.save(filename)

    def solve(self, interleaving):
        """
        Enforce node and arc consistency, and then solve the CSP.
        """
        self.enforce_node_consistency()
        self.ac3()
        if not interleaving:
            print('Solving Crossword with single arc consistency enforcement...')
            return self.backtrack(dict())
        else:
            print('Solving Crossword with interleaved backtracking and arc consistency enforcement...')
            return self.backtrack_ac3(dict())

    def enforce_node_consistency(self):

        # Iterate through all domains
        for domain in self.domains:
            domain_lengrh = domain.length
            to_remove = set()

            # Iterate through all values in the domain
            for val in self.domains[domain]:
                # If value length does not match domain length, add to values to remove
                if len(val) != domain_lengrh:
                    to_remove.add(val)

            # Remove all invalide vals from domain
            self.domains[domain] = self.domains[domain] - to_remove

    def overlap_satisfied(self, x, y, val_x, val_y):
            """
            Helper function that returns true if val_x and val_y
            satisfy any overlap arc consistency requirement for
            variables x and y.

            Returns True if consistency is satisfied, False otherwise.
            """

            # If no overlap, no arc consistency to satisfy
            if not self.crossword.overlaps[x, y]:
                return True

            # Otherwise check that letters match at overlapping indices
            else:
                index_x, index_y = self.crossword.overlaps[x,y]

                if val_x[index_x] == val_y[index_y]:
                    return True
                else:
                    return False

    def revise(self, x, y):
        revision = False
        to_remove = set()

        # Iterate over domains x and y, track any inconsistentcy
        for val_x in self.domains[x]:
            consistent = False
            for val_y in self.domains[y]:
                if val_x != val_y and self.overlap_satisfied(x, y, val_x, val_y):
                    consistent = True
                    break

            if not consistent:
                to_remove.add(val_x)
                revision = True

        # Remove any domain variables that aren't consistent:
        self.domains[x] = self.domains[x] - to_remove
        return revision

    def ac3(self, arcs=None):
        # If no arcs, start with queue of all arcs:
        if not arcs:
            arcs = []
            for domain_1 in self.domains:
                for domain_2 in self.domains:
                    if domain_1 != domain_2:
                        arcs.append((domain_1, domain_2))

        # Continue until no arcs left (arc consistency enforced):
        while arcs:
            domain_x, domain_y = arcs.pop()
            # Revise x domain and y:
            if self.revise(domain_x, domain_y):
                # If x domain is empty after revision, no solution:
                if not self.domains[domain_x]:
                    return False
                # If revised, add to arcs all x neighbors
                for domain_z in self.crossword.neighbors(domain_x) - {domain_y}:
                    arcs.append((domain_z, domain_x))
        return True

    def assignment_complete(self, assignment):
        for domain in self.domains:
            if domain not in assignment:
                return False
        return True

    def consistent(self, assignment):
        processed = []

        for variable_x in assignment:
            value_x = assignment[variable_x]

            # If the assigned word is already used, not consistent:
            if value_x in processed:
                return False
            processed.append(value_x)

            # Check if variable is assigned its length is correct
            if len(value_x) != variable_x.length:
                return False

            # Check if there are conflicts between neighboring variables:
            for variable_y in self.crossword.neighbors(variable_x):
                if variable_y in assignment:
                    value_y = assignment[variable_y]

                    # Check if neighbor variable is assigned and satisfies constraints
                    if not self.overlap_satisfied(variable_x, variable_y, value_x, value_y):
                        return False

        # all assignments are consistent
        return True

    def order_domain_values(self, var, assignment):

        values_ruleout = {val: 0 for val in self.domains[var]}

        # Iterate through all possible values of var:
        for value in self.domains[var]:

            # Iterate through neighboring variables and values:
            for other_var in self.crossword.neighbors(var):
                for other_val in self.domains[other_var]:

                    # If value rules out other value, add to ruled_out count
                    if not self.overlap_satisfied(var, other_var, value, other_val):
                        values_ruleout[value] += 1

        # Return list of vals sorted from fewest to most other_vals ruled out:
        return sorted([x for x in values_ruleout], key = lambda x: values_ruleout[x])
    def select_unassigned_variable(self, assignment):


        # Get set of unassigned variables
        unassigned = set(self.domains.keys()) - set(assignment.keys())

        # Create list of variables, sorted by MRV and highest degree
        result = [var for var in unassigned]
        result.sort(key = lambda x: (len(self.domains[x]), -len(self.crossword.neighbors(x))))

        return result[0]

    def backtrack(self, assignment):

        global BACKTRACK_COUNTER
        global WORDS_TESTED
        BACKTRACK_COUNTER += 1

        # If all variables are assigned, return assignment:
        if self.assignment_complete(assignment):
            return assignment

        # Otherwise select an unassigned variable:
        variable = self.select_unassigned_variable(assignment)
        for value in self.order_domain_values(variable, assignment):
            assignment[variable] = value
            WORDS_TESTED += 1
            if self.consistent(assignment):
                result = self.backtrack(assignment)
                if result:
                    return result
            del assignment[variable]
        return None

    def backtrack_ac3(self, assignment):
        global BACKTRACK_COUNTER
        global WORDS_TESTED
        BACKTRACK_COUNTER += 1

        # If all variables are assigned, return assignment:
        if self.assignment_complete(assignment):
            return assignment

        # Otherwise select an unassigned variable:
        variable = self.select_unassigned_variable(assignment)
        domains_copy = deepcopy(self.domains)
        for value in self.order_domain_values(variable, assignment):
            assignment[variable] = value
            WORDS_TESTED += 1
            if self.consistent(assignment):
                # Update variable domain to be assigned value
                self.domains[variable] = {value}
                # Use ac3 to remove inconcistent values from neighbouring variables
                self.ac3([(other_var, variable) for other_var in self.crossword.neighbors(variable)])
                result = self.backtrack_ac3(assignment)
                if result:
                    return result
            # If assignment does not produce solution, remove assignment and reset domains
            del assignment[variable]
            self.domains = domains_copy
        return None

def main():

    # Check usage
    if len(sys.argv) not in [4, 5]:
        sys.exit("Usage: python generate.py structure words interleaving [output]")

    # Parse command-line arguments
    structure = sys.argv[1]
    words = sys.argv[2]
    interleaving = sys.argv[3] == 'True'
    output = sys.argv[4] if len(sys.argv) == 5 else None

    # Generate crossword
    crossword = Crossword(structure, words)
    creator = CrosswordCreator(crossword)
    assignment = creator.solve(interleaving)

    # Print result
    if assignment is None:
        print("No solution.")
    else:
        print("Calls to backtrack function: ", BACKTRACK_COUNTER)
        print("Words tested to find solution: ", WORDS_TESTED)
        creator.print(assignment)
        if output:
            creator.save(assignment, output)


if __name__ == "__main__":
    main()
