var _ = require('underscore');

var FAILURE = -1;

////////// DEFINITIONS //////////
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


//#############################################
/////// UTILITY FUNCTIONS ////////////////////
//#############################################

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

function isAssigned(dom) {
    return dom.length == 1;
}

function getAssigned(vars) {
    return _.chain(vars)
        .filter(isAssigned)
        .flatten().value();
}

//#############################################
//// CONSTRAINT DEFINITIONS //////////////////
//#############################################

// function(scope, optional) return boolean

    var SAME = function(a, b) {
        return a === b;
    }

    var VALUE = function(a, val) {
        return a === val;
    }

    // vars is an array of domain arrays!! 
    var ALL_DIFF = function(vars) {
        var modified = false;

        // separate variables already assigned
        var assigned = getAssigned(vars);
        while(assigned.length !== 0) {
            vars = _.chain(vars)
                .reject(isAssigned) // remove them from original
                .map(function(vDomain){
                    return _.difference(vDomain, assigned);
                }).value();

            assigned = getAssigned(vars); // check again for singletons
        }
    }


//#############################################
////////// PROBLEM DEFINITION ////////////////
//#############################################
  

csp.prototype.solve = function() {
    var assignment = {}; 
    _.each(this.variables, function(name){assignment[name]=domain.splice();});
    var solution = this.backTrack(assignment);
    if(solution !== FAILURE && solution instanceof Array)
        alert("Solved!\n"+solution);
}

// are all variables assigned?
csp.prototype.isComplete = function(assignment) {
    return getAssigned().length === this.variables.length;
}

csp.prototype.backTrack(assignment) {
    if(this.isComplete(assignment)) return assignment;

    var considered = getMostConstrainedVar(); // FIXME

    var snapshot = considered;
    for(var val in this.domain) {
        if(val in considered){
            var inference = {};
            assignment[considered.name] = _reject();

            // INFERENCE
            // END INFERENCE

        }
        // completely revert
        assignment.frontier[vrb] = snapshot; // FIXME this does not revert inferences!!!!
    }
    return FAILURE;
}



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

