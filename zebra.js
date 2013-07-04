var people = ["englishman", "spaniard", "norwegian", "ukrainian", "japanese"];
var pets = ["dog", "zebra", "fox", "snail", "horse" ];
var colors = ["green", "blue", "yellow", "red", "ivory"];
var drinks = ["coffee", "water", "oj", "milk", "tea"];
var candies = ["kit-kat","smarties","snickers","hersheys","milky-way"];

var NUM_HOUSES = 5;

var FAILURE = -1;

var CHECK=0, FORCE=1;
var RIGHT=0, NEXT=1, SAME=2, ALL_DIFF=3, LOCATED=4; // ALL_DIFF replaced DIFF 
var relations = [];
relations[RIGHT][CHECK] = function(a, b) {
//    return getIndex(a) === getIndex(b)-1;
    return false; // these may not need to exist
}
relations[RIGHT][FORCE] = function(assignment) {
    if(this.check()) return; // already correctly set

    var idx = getIndex(this.left);
    if(idx !== null) {
        if(idx+1 < assignment.length && this.right['val'] in assignment[idx+1][this.right['var'])
            assignment[idx+1][this.right['var'] = [ this.right['val'] ];
        else throw "Constraint Violation"; 
    } else {
        // try the converse
        idx = getIndex(this.right);
        if(idx !== null) {
            if(idx > 0 && this.left['val'] in assignment[idx-1][this.left['var'])
                assignment[idx-1][this.left['var'] = [ this.left['val'] ];
            else throw "Constraint Violation"; 
        }
    }
}
relations[NEXT] = function(a, b) {
    return (getIndex(a) === getIndex(b)-1) || (getIndex(a) === getIndex(b)+1);
}
relations[SAME] = function(a, b) {
    return getIndex(a) === getIndex(b);
}
relations[ALL_DIFF][CHECK] = function() {

}
// Does not handle the case where {x y} remains but only one slot is to be selected.  TODO handle
relations[ALL_DIFF][FORCE] = function(assignment) {
    var vars;
    for(var v in this.domains)
        vars[v] = [];
    
    var idx;
    var mustContinue = false;
    do {
        for(int x=0; x<assignment.length; x++) {
            for(var vrb in vars {
                if(assignment[x][vrb].length < 1 ) {
                    throw "Failure"; // domain empty
                } else {
                    // if this variable has an assignment
                    if(assignment[x][vrb].length === 1) {

                        // if not elsewhere assigned
                        if(assignment[x][vrb][0] in vars[vrb])
                            vars[vrb].push(assignment[x][vrb][0]); // note this assignment
                        else throw "Constraint Violation"; // not unique!

                    } else { 
                        // variable is not assigned
                        // remove all previously selected values from domain
                        for(var str in vars[vrb]) {
                            var i=assignment[x][vrb].indexOf(str);
                            if(i != -1) assignment[x][vrb] = assignment[x][vrb].splice(i, i+1);
                            mustContinue = true; // another check for consistency (will also catch empty domain)
                            // consider full constraint loop continuation instead of local contination
                        }
                    }
                }
            }
        }
    } while(mustContinue);

}
relations[LOCATED][CHECK] = function(a, b) {
    //return getIndex(a) === b;
    // NO LONGER CORRECT STRATEGY
}
relations[LOCATED][FORCE] = function(assignment) {
    var variable = this.left['var'];
    var value = this.left['val'];
    var idx = this.right['val'];
     if(typeof idx  !== "number") return; // TODO determine correct return value for failed constraints
     if(getIndex(this.left) !== null) { // TODO clean up logic, inefficient
        if(assignment[idx][variable][0] !== value)
            throw "Constraint Violation";
        else return; // already correctly set
    } else 
        assignment[idx][variable] = [ value ]; // TODO set REVISED or something to trigger more consistency checks
}


// TODO verify that recursion works, otherwise must undo the following actions
function getAssignment() {
    var slots = new Array(NUM_HOUSES);
    for(var x = 0; x < NUM_HOUSES; x++) 
        slots[x] = new house();
    return slots;
}

function house(domains) {
    this.frontier = {};
    for(var d in domains)
        this.frontier[d] = domains[d].slice();
}


function getIndex(cnst) {
    var assignment = GET_ASSIGNMENT(); // PULL THIS IN CORRECTLY
    if(!cnst['var']) return null;

    var idx;
    for(int x = 0; x < assignment.length; x++) {
        var cur = assignment[x][cnst['var']];
        if(cur instanceof Array && cur.length === 1 && cur[0] === cnst['val']) {
            idx = x;
            break;
        }
    }
    return idx || null; // not yet set or not found
}

// constraint: ["var:value", "var:value", function]
var csp = function(domains, constraints) {
    this.domains = domains;
    this.constraints = [];
    for(cc in constraints) 
        this.constraints.push(this.getConstraint.apply(null, constraints[cc]));
}

// accepts var:value, with a1 being the pivot
csp.prototype.getConstraint = function(a1, a2, constraint) {
    var cnst = {};

    var left = {};
    left['var'] = typeof a1 == "string" ? a1.split(':')[0] : undefined;
    left['val'] = left['var'] !== undefined ? a1.split(':')[1] : a1;
    var right = {};
    right['var'] = typeof a2 == "string" ? a2.split(':')[0] : undefined;
    right['val'] = right['var'] !== undefined ? a2.split(':')[1] : a2;

    cnst.left = left;
    cnst.right = right;

    cnst.check = function() {
        return function(){
            return relations[constraint].call(cnst, left, right); // arguments will not be necessary
        }
    }

    // TODO create force method
}



csp.prototype.solve = function() {
    var solution = backTrack(getAssignment());
    if(solution !== FAILURE && solution instanceof Array)
        alert("Solved!"); // handle representation
}

csp.prototype.backTrack(assignment) {
    if(isComplete(assignment)) return assignment;
    // must find the most constrained variable, where variable comprises both a variable AND an index
    var vArray = getMostConstrainedVar(); // unique variable: [idx, name] 

    // above could also flatten variables, using idx as the value of each with additional constraints

    var vDomain = assignment[vArray[0]][vArray[1]]; 

    // TODO order values by degrees of freedom
    // Will require dynamic behavior such that constraining values have been added to NEIGHBORS
    var snapshot = vDomain;
    for(var val in this.domains) {
        if(val in vDomain {
            assignment[vrb] = snapshot.slice(val, val+1); // effectively sets the value

            // INFERENCE
            try {
                var revised = false;
                while(revised) {
                    // Go through and force all constraints
                    for(cc in this.constraints) 
                        revised = this.constraints[cc].force() || revised; // only revised if true
                }
            } catch(e) {
                console.error(e); // either handle specifically or convert to boolean
                // FIXME this is not correct, I would still have to revert changes before backtracking
                return FAILURE;
            }
            // END INFERENCE

        }
        // completely revert
        assignment.frontier[vrb] = snapshot; // FIXME this does not revert inferences!!!!
    }
    return FAILURE;
}

// If one remaining value for all variables, success
function isComplete(assignment) {
    for(var i=0; i<assignment.length; i++) {
        for(var vrb in assignment) {
            var variable = assignment[vrb];
            if(!variable || !(variable instanceof Array) 
                    || variable.length !== 1)
                return false;
        }
    }
    return true;
}

var getMostConstrainedVar = function getRandomVar() { // lol
    // TODO implement
}



////////// ACTUALLY RUN THE PROBLEM //////////
var domains = {}
domains['person'] = people;
domains['pet'] = pets;
domains['color'] = colors;
domains['drink'] = drinks;
domains['candy'] = candies;

var constraints = [
    [ "person:englishman", "color:red", SAME ],
    [ "person:spaniard", "pet:dog", SAME ],
    [ "person:norwegian", 0, LOCATED ],
    [ "color:ivory", "color:green", RIGHT ],
    [ "candy:hershey", "pet:fox", NEXT ],
    [ "candy:kit-kat", "color:yellow", SAME ],
    [ "person:norwegian", "color:blue", NEXT ],
    [ "candy:smarties", "pet:snail", SAME ],
    [ "candy:snickers", "drink:oj", SAME ],
    [ "person:ukrainian", "drink:tea", SAME ],
    [ "person:japanese", "candy:milkey-way", SAME ],
    [ "candy:kit-kat", "pet:horse", NEXT ],
    [ "drink:coffee", "color:green", SAME ],
    [ "drink:milk", 2, LOCATED ]
];
var problem = csp(domains, constraints);

