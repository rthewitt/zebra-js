/*
 * I intend to create a bipartite graph from variables->values from the hypergraph.
 * Doing so will allow me to find a matching, and satisfy the arc-consistency
 * in regards to the AllDiff constraint.
 */
var _ = require('underscore');

var FAILURE = -1;
var CNST = 0;

////////// DEFINITIONS //////////
var people = ["englishman", "spaniard", "norwegian", "ukrainian", "japanese"];
var pets = ["dog", "zebra", "fox", "snail", "horse" ];
var colors = ["green", "blue", "yellow", "red", "ivory"];
var drinks = ["coffee", "water", "oj", "milk", "tea"];
var candies = ["kit-kat", "smarties", "snickers", "hershey", "milky-way"];

var domain = [1, 2, 3, 4, 5];
var variables = [].concat(people, pets, colors, drinks, candies);



//#############################################
/////// GRAPH DATA STRUCTURE /////////////////
//#############################################

// TODO create domain node and regular vertex?
var Vertex = function(info) {
    this.id = _generateID(); // HANDLE COLLISIONS
    this.info = info;
    this.domain = [];
    //this.edges = [];
    this.constraints = [];
    this.connections = []; // TODO handle removal case maybe
};

// Change implementation such that constraint _is_ an Edge
Vertex.prototype = {
    id: null,
    connections: null, // a set of unique ids of Edges
    info: null,
    //edges: null,
    domain: null,
    constraints: null,
    addAssignment: function(assn) {
        if(!(assn.id in this.connections)) {
            this.connections.push(assn.id);
            this.domain.push(assn);
            //this.edges.push(assn); // TODO see if this is ever actually used, delete
        } else console.warn('Duplicate UUID found in addAssignment');
    },
    addConstraint: function(cnst) {
        if(!(cnst.id in this.connections)) {
            this.connections.push(cnst.id); // is this check redundant?
            this.constraints.push(cnst);
            //this.edges.push(cnst);
        }
    }
}

var Edge = {
    from: null,
    to: null,
    weight: null, // represents flow, softness of constraints
    capacity: null, // flow networks
    isValidEdge: function() {
        return this.to instanceof Array && this.to.length > 0 && 
            this.from instanceof Array && this.from.length > 0;
    }
};

var UNARY=1, BINARY=2, NARY=3;
// if graph ever becomes dynamic, we'll need to manage scope or rely on traversal
// to determine variable dependence.  (Preferred)
var Constraint = function(type, relation, scope, weight) {
    this.id = _generateID(); // HANDLE COLLISIONS
    this.scope = scope;  
    this.type = type;
    this.weight = weight || 0; // sort or hard?
    this.check = function() { 
        var params = Array.prototype.slice.call(arguments);
        return relation.apply(this, params);
    }
};
Constraint.prototype = Edge;

var Assignment = function(valNode, capacity) {
    this.id = _generateID(); // HANDLE COLLISIONS
    this.to = [valNode];
    this.capacity = capacity || 1; // Flow network analysis
};
Assignment.prototype = Edge;
var Graph = {
    vertices: null,
    edges: null,
    directed: false,
    addEdges: function() {
        var edges = Array.prototype.slice.call(arguments);
        _.each(edges, function(edge){
            if(!(edge in this.edges))
                this.edges.push(edge);
        });
    }
};

var FlowProto = {
    source: null,
    sink: null,
    flow: null,
    initializeFlow: function (flush) {
        this.flow = this.flow || {};
        // weight represents flow in this graph
        _.each(this.edges, function(edge) {
            edge.weight = edge.weight && !flush ? edge.weight : 0;
            this.flow[edge.id] = edge.weight;
        });
    }
};
FlowProto.prototype = Graph;

// TODO require an ID on vertices/edges as a means of key
// TODO add constraints/variables as array, for sorting purposes?
// (currently using map on csp object)
var ConstraintGraph = function (vertices, directed) {
    this.vertices = vertices || [];
    this.directed = directed || false;
};
ConstraintGraph.prototype = Graph;

//var BipartiteFlowGraph = function(vertices, edges, domain) {
var BipartiteFlowGraph = function(source, reversedSink, directed) {
    var self = this;
    this.vertices = [];
    _.each(reversedSink.edges, function(edge){
        var domainNode = edge.to[0];
        // TODO add edges as I go?
        domainNode.addAssignment(sink);
        if(!self.directed) {
            // delete sink->domain edges 
        } else {} // add the reverse edge to colleciton otherwise
        self.vertices.push(domainNode);
    });
    _.each(source.edges, function(edge){
        var rangeNode = edge.to[0];
        self.vertices.push(rangeNode);
        self.edges.push(edge);
        self.addEdges(rangeNode.domain);
    });
    this.edges = edges || [];
    this.flow = vertices || {}; // named array

    // add reduce
    // add complement (reverse edges from domain)
    // add flush
}
BipartiteFlowGraph.prototype = FlowProto;



var getConstraint = function(scope, rel, optional) {
    var type = (scope.length > 2 ? NARY : (scope.length < 2 ? UNARY : BINARY));
    var from = scope[0]; // is this ever used?
    var check = typeof optional === 'undefined' ? rel : rel.apply(null, optional); // we're looking for a closure

    // to is set in hypergraph, head in directed domain subgraph
    var to = type === UNARY ? [from] : scope.slice();
    var cnst = new Constraint(type, check, scope);
    cnst.to = to;
    cnst.from = from;
    return cnst;
}


//#############################################
/////// UTILITY FUNCTIONS ////////////////////
//#############################################

function computeMaximalMatching(vars) {
    var source = new Vertex(null);
    var sink = new Vertex(null);
    //var dom = _.chain(vars).map(function(v){return v.edges}).unique().value();
    var flowGraph = new FlowGraph(vars);
    // add source vertex
    // add sink vertex
    // for each variable passed in
    // -add edge from source to variable
    // -append edge to collection
    // -for all edges in variable
    // -append edge to collection
    // -if domain val does not have edge->sink, add one and append to collection
    
    // call maxFlow(source, vertex); -- consider this
    // if flow < numberOfVariablesPassIn
    // return false;
    // else if flow === number... // unnecessary
    // IMPORTANT - add reverse edges FOR EACH EDGE IN MATCHING if not already added (why???)
    // decomposeSubGraph(graph); // use Tarjan's algorithm
    // for all edges from variablesPassedIn -> domain WITHOUT flow (not in matching)
    // if edge not in matching
    //      component = component containing edge.from
    //      if(!(edge.to[0] in component))
    //          PRUNE_EDGE_FROM_DOMAIN(); // !!

    // remove/delete source vertex. (Do edges need to be explicitly deleted?)
    // remove/delete edges from variable to sink, unless we want to persist these
    // remove sink, unless we want to persist sink
}

function findPath(source, sink, path) {
    // if source === sink
    //      return path
    // for edge in this.edges (I'll use findPath.call({edges: coll}, s,t,path)
    //      residual = edge.capacity - self.flow[edge] // WHY USE SELF (GRAPH?)
    //      if(residual > 0 && !(edge in path) // says (edge, residual) - does that matter?
    //      create new array with path+edge
    //      result = findPath.call(this, edge.to[0], sink, newpath);
    //          if(result)
    //              return result;
}

// TODO conditionally add edges to matching
function maxFlow(source, sink) {
    var graph = {edges: null, flow: null};
    var path = findPath.call(source, sink, []);

    while(path) {
        // I think this will work as a min function
        var minFlow = _.reduce(path, function(minFlow, step){
            return step.res < minFlow ? step.res : minFlow;
        }, Infinity);

        // Merge path flow into 
        _.each(path, function(step){
            if(typeof graph.flow[step.edge] === 'undefined') { // TODO ensure flow initialized, delete
                graph.flow[step.edge] += minFlow; // WHAT?
                // same for redge - decide when to add that
            }
        });
        path = findPath.call(source, sink, []);
    }

    // sum of flow for flow in edges from source, == maximal matching number (k)
    return _.chain(source.domain) // TODO change all domain to edge or assignment?
        .map(function(edge){return graph.flow[edge];})
        .reduce(function(sum, f){return sum+f;})
        .value();
}

function _generateID () {
      var S4 = function() {
         return (((1+Math.random())*0x10000)|0).toString(16).substring(1);
      };
      return (S4()+S4()+"-"+S4()+"-"+S4()+"-"+S4()+"-"+S4()+S4()+S4());
}

function hasDomainValue(vrb, val) {
    for(var d in vrb.domain) {
        var assn = vrb.domain[d];
        if(assn)
            for(var valNode in assn.to) {
                if(assn.to[valNode].info === val)
                    return true;
            }
    }
    return false;
}

function forceSelection(vrb, val) {
    function relevant(edge) {
        if(edge.to.length !== 1) throw "Assignment has wrong dimentionality";
        return edge.to[0].info === val.info;
    }
    var assignment = _.filter(vrb.domain, relevant);
    if(assignment.length !== 1) throw "Duplicate Domain!";
    var inf = [{
        variable: vrb,
        edges: _.reject(vrb.domain, relevant)
        }];
    vrb.domain = assignment;
    return inf;
}

function queueAffectedNodes(Q, vNode, spent) {
    console.log('CSP was revised - ' + vNode.info + ' as pivot.');
    _.each(vNode.constraints, function(cnst){
        var slot = [cnst];
        var members = _.without(cnst.to, vNode, spent);
        if(members.length > 0) {
            slot.push(_.without(cnst.to, vNode, spent));
            Q.push(slot);
        }
    });
}

// returns in form: [constraint, [args...]]
function initializeQueue(constraints, Q) {
    if(Q instanceof Array)  {
        var arcs = _.map(constraints, function(cnst){
            return [cnst, _.unique(cnst.to.slice())] // TODO understand why there were duplicates.  (Should have been directional)
        });
        Q.push.apply(Q, arcs);
    } else console.error('Bad Q');
}

//#############################################
//// CONSTRAINT DEFINITIONS //////////////////
//#############################################

// function(scope, optional) return boolean

    var SAME = function(a, b) {
        return a.info === b.info;
    }

    // will return a closure
    var VALUE = function(val) {
        return function(a) {
            //debugger;
            return a.info === val;}
    }

    // TEMPORARY
    var RIGHT = function(a, b) {
        return b.info-a.info === 1;
    }
    var NEXT = function(a, b) {
        return Math.abs(b.info-a.info) === 1;
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
                    console.log("FILTERING: modified was: "+modified); // verify closure behavior
                    var filtered = _.difference(vDomain, assigned);
                    if(filtered.length !== vDomain.length)
                        modified = true; 
                    return filtered;
                }).value();

            assigned = getAssigned(vars); // check again for singletons
        }
        return modified;
    }

//#############################################
////////// ALT. CONSISTENCY ALGORITHMS  //////
//#############################################


function ac3(csp, inferences) {
    console.log("AC3 running...");
    var Q = []; 
    initializeQueue(csp.cMap[UNARY], Q);
    initializeQueue(csp.cMap[BINARY], Q);
    //initializeQueue(csp.cMap[NARY], Q);
    
    while(Q.length > 0) {
        var arc = Q.shift();
        if(typeof arc === undefined) continue; // FIXME avoid pushing undefined arcs
        var v1 = arc[1][0], v2=arc[1][1];

        switch(parseInt(arc[CNST].type)){
            case UNARY:
            case BINARY:
                if(csp.revise(arc[0], inferences, arc[1])) {
                    if(v1.domain.length === 0) 
                        return FAILURE; 
                    queueAffectedNodes(Q, v1, v2);
                }
                break;
            case NARY:
                // TODO implement
                break;
            default:
                break;
        };
    }
    return true;
}



//#############################################
////////// PROBLEM DEFINITION ////////////////
//#############################################
  
var csp = function(variables, domain, constraints) {
    var self = this;
    this.stats = { depth: 0, max: 0, inf: 0, backtracks: 0, time: null};
    this.domain = _.map(domain, function(val){return new Vertex(val);});
    this.vMap = {}; // ONLY WORKS WITH STRINGS / UUIDS!!!
    this.numVars = variables.length;
    _.each(variables, function(v){
        self.vMap[v] = new Vertex(v);
    });

    var cMap = {};
    cMap[UNARY] = [];
    cMap[BINARY] = [];
    cMap[NARY] = [];
    this.cMap = cMap; // Later
    
    _.each(constraints, function(cc){
        var params = cc.slice();
        params[0] = _.map(cc[0], function(varName){return self.vMap[varName]}); 
        var cnst = getConstraint.apply(self, params);
        cMap[cnst.type].push(cnst);
    });


    // before building, we want all variables in vMap, all edges (constraints+assignments)
    this.buildConstraintGraph();

    // TODO sort variables by inspecting constraints
}

csp.prototype.solve = function() {
    var assignment = {}; 
    _.each(this.vMap, function(node){assignment[node.info]=node});

    var start = new Date().getMilliseconds()
    var solution = this.backTrack(assignment);
    this.stats.time = new Date().getMilliseconds() - start;

    if(solution !== FAILURE) {
        console.log("\n\nSolved in "+
                (this.stats.time < 1000 ? this.stats.time+" ms" : this.stats.time/1000+" seconds") + "!" +
                "\ndepth: "+this.stats.depth +
                "\nmax depth: "+this.stats.max +
                "\ninferences: "+this.stats.inf +
                "\nbacktracks: "+this.stats.backtracks+"\n\n\n");
        printSolution(solution);
    } else console.log("Failed to find a solution");
}

function printSolution(sol) {
    for(var v in sol) {
        var str = v+': ';
        for(var d in sol[v].domain) 
            str+=sol[v].domain[d].to[0].info+' ';
        console.log(str);
    }
}

// binary only????
csp.prototype.revise = function(cnst, inferences, params) {
    var pivotVar = params[0];
    var modified = false;
    // if no value for v2 exists in C(v1,v2), remove v1 from domaim
    _.each(pivotVar.domain, function(assnEdge){
        var found=false;
        var pivotVal = assnEdge.to[0];
        var targetVar = parseInt(cnst.type) === UNARY ? pivotVar : params[1]; // UGLY unary case
        for(var tv in targetVar.domain) {
            var targetVal = targetVar.domain[tv].to[0]; // domain node
            if(cnst.check(pivotVal, targetVal)) { // is ordering preserved?
                //debugger;
                found = true;
                break;
            }
        }
        if(!found) {
            pivotVar.domain = _.without(pivotVar.domain, assnEdge);
            // TODO MAKE THIS MORE COMPACT
            inferences.push({variable: pivotVar, edges: [assnEdge]});
            modified = true;
        }
    });
    return modified;
}

csp.prototype.revert = function(inferences) {
    this.stats.backtracks++;
    console.log('REVERTING');
    if(!inferences) return;
    while(inferences.length > 0) {
        var inf = inferences.pop();
        _.each(inf.edges, function(edge){inf.variable.domain.push(edge);});
    }
}

// TODO use array, not map, and sort on the array during csp construction
csp.prototype.getMostConstrainedVar = function() {
    var most; // most so far
    for(var name in this.vMap) {
        var variable = this.vMap[name];

        if(!variable instanceof Vertex || variable.domain.length < 2)  // Debugging only, TODO delete
            continue;

        if(!most || 
                variable.constraints.length > most.constraints.length) 
            most = variable;
    }
    if(most)
        console.log('most: '+most.info +' with '+most.constraints.length+' constraints');
    return most || null;
}

// In my hypergraph formulation, inferences are simply edges in the
// bipartite variable->value representation
// A "{var = value}" assignment can be represented by its inverse,
// the set of edges removed in order to specify the assignemnt.
// In this way, state reparation is very straightforward.
csp.prototype.backTrack = function(assignment) {
    this.stats.depth++;
    if(this.stats.depth > this.stats.max)
        this.stats.max = this.stats.depth;

    var considered = this.getMostConstrainedVar();

    if(considered === null) 
        return assignment;

    //console.log('considering '+considered.info);
    var inferences;

    for(var vn in this.domain) {
        var valNode = this.domain[vn];
        //console.log('valNode.info = '+valNode.info);
        if(hasDomainValue(considered, valNode.info)) {
            // verify boundary conditions
            inferences = forceSelection(considered, valNode);
            //debugger;
            var ret = this.infer(assignment, inferences);
            if(ret !== FAILURE) { 
                var recur = this.backTrack(assignment);
                if(recur !== FAILURE)
                    return recur;
            } else {
                console.log('backtracking');
                this.stats.backtracks++;
                this.stats.depth = 0;
            }
        }
        // completely revert
        this.revert(inferences); // adds the edges back into the graph
    }
    debugger;
    return FAILURE;
}

csp.prototype.infer = function(assignment, inferences) {
    this.stats.inf++;
    return ac3.call(null, this, inferences);
}

// Considering reworking inheritance here
csp.prototype.buildConstraintGraph = function() {
    console.log('Building Constraint Graph');
    // vertices: come directly from constraints
    //this.graph = new ConstraintGraph(v,e,d);

    var self = this;
    console.log('Number of unary constraints: '+self.cMap[UNARY].length);
    console.log('Number of binary constraints: '+self.cMap[BINARY].length);
    console.log('Number of nary constraints: '+self.cMap[NARY].length);

    var vertices = [];
    // consider adding constraint/assignment arrays

    _.each(this.vMap, function(varNode){
        vertices.push(varNode); // add to graph collection
        _.each(self.domain, function(valNode){
            var ass = new Assignment(valNode);
            varNode.addAssignment(ass);
        });
    });

    for(var type in this.cMap){
        switch(parseInt(type)) {
            case UNARY:
                break;
            case BINARY:
                _.each(this.cMap[type], function(cc){
                    for(var i=0; i<cc.scope.length; i++) {
                        //if(!cc.scope[i]) continue; - FIXED TODO remove if verified
                        var vertex = self.vMap[cc.scope[i].info]; // get from the collection
                        cc.to.push(vertex);
                        var others = _.without(cc.scope, vertex.info);
                        _.each(others, function(affected){
                            vertex.addConstraint(cc);
                        });
                    }
                });
                break;
            case NARY:
                break;
            default:
                break;
        }
    }

    // NEED VERTICES, --- CHANGED --- from: EDGES -- future: Constraints, Assignments
    var graph = new ConstraintGraph(vertices);
}


var constraints = [
    [ ["englishman", "red"], SAME ],
    [ ["spaniard", "dog"], SAME ],
    [ ["norwegian"], VALUE, [1]],
    [ ["ivory", "green"], RIGHT ],
    [ ["hershey", "fox"], NEXT ],
    [ ["kit-kat", "yellow"], SAME ],
    [ ["norwegian", "blue"], NEXT ],
    [ ["smarties", "snail"], SAME ],
    [ ["snickers", "oj"], SAME ],
    [ ["ukrainian", "tea"], SAME ],
    [ ["japanese", "milky-way"], SAME ],
    [ ["kit-kat", "horse"], NEXT ],
    [ ["coffee", "green"], SAME ],
    [ ["milk"], VALUE, [3]]
];

var problem = new csp(variables, domain, constraints);
problem.solve();
