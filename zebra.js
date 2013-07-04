var _ = require('underscore');

var NUM_HOUSES = 5;

var FAILURE = -1;

var relations = [];

function getAssignment() {
    var slots = new Array(NUM_HOUSES);
    for(var x = 0; x < NUM_HOUSES; x++) 
        slots[x] = new house();
    return slots;
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






////////// ACTUALLY RUN THE PROBLEM //////////
var people = ["englishman", "spaniard", "norwegian", "ukrainian", "japanese"];
var pets = ["dog", "zebra", "fox", "snail", "horse" ];
var colors = ["green", "blue", "yellow", "red", "ivory"];
var drinks = ["coffee", "water", "oj", "milk", "tea"];
var candies = ["kit-kat","smarties","snickers","hersheys","milky-way"];

var domain = [1, 2, 3, 4, 5];
var variables = [].concat(people, pets, colors, drinks, candies);

var UNARY=1, BINARY=2, NARY=3;
function constraint(t, r, s){this.type = t; this.force = r || function(){}; this.scope = s || [];}
var unary = new constraint(UNARY);
var binary = new constraint(BINARY);
var nary = new constraint(NARY);
// ORDER CONSTRAINT ARRAY BY TYPE DURING EXECUTION!!!!!!  

function getConstraint(scope, rel, optional) {
    var c = function(){};
    c.prototype = (scope.length > 2 ? nary : (scope.length < 2 ? unary : binary));
    function f(args) {
        return function(){return rel.apply(this, args)}
    }
    var args = optional || [];
    c.force = f(this.scope.concat(args)); // in case unary/nary with arguments
    return c;
}


//// CONSTRAINT DEFINITIONS
// 
    var SAME = function(a, b) {
        return a === b;
    }

    var VALUE = function(a, val) {
        return a === val;
    }

    // global
    var ALL_DIFF = function(vars) {
        var diff = true;
        for(var i=0; i<vars.length-1; i++) 
            diff = diff && vars[i]===vars[i+1];
        return diff;
    }
// 
///////////////////////////
  

csp.prototype.solve = function() {
    var assignment = {}; 
    _.each(this.variables, function(name){assignment[name]=domain.splice();});
    var solution = this.backTrack(assignment);
    if(solution !== FAILURE && solution instanceof Array)
        alert("Solved!\n"+solution);
}

csp.prototype.backTrack(assignment) {
    if(isComplete(assignment)) return assignment;

    // TODO order this, or create function
    var considered = getMostConstrainedVar(); 

    // TODO order values by degrees of freedom
    var value = this.variables[0];

    // Will require dynamic behavior such that constraining values have been added to NEIGHBORS
    var snapshot = considered;
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




// TODO use _.reject to remove same the value from 

// function(scope, optional) return boolean

var constraints = [
    [ ["englishman", "red"], SAME ],
    [ ["spaniard", "dog"], SAME ],
    [ ["norwegian"], VALUE, 0],
    [ ["ivory", "green"], RIGHT ],
    [ ["hershey", "fox"], NEXT ],
    [ ["kit-kat", "yellow"], SAME ],
    [ ["norwegian", "blue"], NEXT ],
    [ ["smarties", "snail"], SAME ],
    [ ["snickers", "oj"], SAME ],
    [ ["ukrainian", "tea"], SAME ],
    [ ["japanese", "milkey-way"], SAME ],
    [ ["kit-kat", "horse"], NEXT ],
    [ ["coffee", "green"], SAME ],
    [ ["milk"], VALUE, 2]
];
var problem = csp(domains, constraints);

var csp = function(variables, domain, constraints) {
    this.domain = domain;
    this.variables = variables;
    this.constraints = [];
    _.each(constraints, function(cc){
        this.constraints.push(getConstraint.apply(this, cc);
    });
    // sort variables by inspecting constraints
    // for each constraint, for each in scope push unique others in scope
    //this.neighbors = _.map();
}

