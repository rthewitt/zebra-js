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

/* var Edge = {
    from: null,
    to: null,
    weight: null, // represents flow, softness of constraints
    capacity: null, // flow networks
    isValidEdge: function() {
        return this.to instanceof Array && this.to.length > 0 && 
            this.from instanceof Array && this.from.length > 0;
    }
}; */
var Edge = function() {
    this.from = null;
    this.to = null;
    this.weight = null;
    this.capacity = null;
    this.isValidEdge = function() {
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
Constraint.prototype = new Edge();
Constraint.prototype.constructor = Constraint;

var Assignment = function(valNode, capacity) {
    this.id = _generateID(); // HANDLE COLLISIONS
    this.to = [valNode];
    this.capacity = capacity || 1; // Flow network analysis
};
Assignment.prototype = new Edge();
Assignment.prototype.constructor = Assignment;

var Graph = function(v, e, d) {
    this.vertices = v || [];
    this.edges = e || [];
    this.directed = d || false;
    this.addEdges = function() {
        var edges = Array.prototype.slice.call(arguments);
        var self = this;
        _.each(edges, function(edge){
            if(edge === 'weight') console.log('FUCK');
            if(!(edge in self.edges))
                self.edges.push(edge);
        });
    };
}
var tmpGraph = function(){};
tmpGraph.prototype = Graph.prototype;

// TODO add constraints/variables as array, for sorting purposes?
// (currently using map on csp object)
var ConstraintGraph = function (vertices, directed) {
    Graph.call(this, vertices, null, directed);
};
ConstraintGraph.prototype = new tmpGraph();
ConstraintGraph.prototype.constructor = ConstraintGraph;

// TODO add domain in parallel to vertices, alias vertices->range?
// TODO add complement (reverse edges from domain)
var BipartiteFlowGraph = function(source, reversedSink, directed) {
    console.log('reverse links: '+reversedSink.domain.length);

    Graph.call(this, null, null, directed); 
    this.source = source;
    this.sink = null; // reminder to fix it first
    this.flow = {};
    this.flomain = []; // TODO decide if this handle is necessary
    this.flow = {};

    var self = this;
    _.each(reversedSink.domain, function(redge){
        var domainNode = redge.to[0];
        var sinkLink = new Assignment(reversedSink);
        domainNode.addAssignment(sinkLink);

        if(!self.directed)  
            reversedSink.domain = []; // delete sink->domain edges 
        else 
            self.addEdges(redge); // TODO verify bidirectionality during flow algorithm

        self.addEdges(sinkLink);
        self.vertices.push(domainNode);
    });

    _.each(source.domain, function(edge){
        var rangeNode = edge.to[0];
        self.vertices.push(rangeNode);
        self.edges.push(edge);
        self.addEdges.apply(self, rangeNode.domain);
    });

    function initializeFlow (flush) {
        this.flow = this.flow || {};
        // weight represents flow in this graph
        var graph = this;
        _.each(this.edges, function(edge) {
            edge.weight = edge.weight && !flush ? edge.weight : 0;
            graph.flow[edge.id] = edge.weight;
        });
    };

    initializeFlow.call(this, true); // here is a good a place as any

    // Removes the sink. Consider the source as well.
    this.destruct = function() {
        _.each(this.flomain, function(node){node.to = [];});
        // delete anything that stays in memory
    };

    this.flush = function() { return initializeFlow.call(this, true); };

    this.maxFlow = function(source, sink) {
        var self = this;
        var path = this.findPath(source, sink, []);

        // path in form [{ edge: edge, res: residualFlow }, ...]
        while(path && path.length > 0) { // TODO verify fix was necessary
            // I think this will work as a min function
            var minFlow = _.reduce(path, function(minFlow, step){
               return step.res < minFlow ? step.res : minFlow;
            }, Infinity);

            // Merge path flow into graph - this blocks when unit flow is capacity!
            _.each(path, function(step){ self.flow[step.edge.id] += minFlow; });

            path = this.findPath(source, sink, []);
        }

        // sum of flow for flow in edges from source, == maximal matching number (k)
        return _.chain(source.domain) // TODO change all domain to edge or assignment?
            .map(function(edge){return self.flow[edge.id];})
            .reduce(function(sum, f){return sum+f;})
            .value();
    };

    this.findPath = function (src, dst, path) {
        if(src === dst || src.id === dst.id) 
            return path;

        var self = this;
        for(var i=0; i<src.domain.length; i++) {
            var edge = src.domain[i];
            var residual = edge.capacity - self.flow[edge.id];  // Equivalent to edge weight

            var inPath = false;
            for(var step in path) {
                if(path[step].edge.id === edge.id)
                    inPath = true;
            }

            if(residual > 0 && !inPath) {
                var newPath = path.concat([{ edge: edge, res: residual }]);
                var result = self.findPath(edge.to[0], dst, newPath);
                if(result)
                    return result;
            }
        }
    };
}
BipartiteFlowGraph.prototype = new tmpGraph();
BipartiteFlowGraph.prototype.constructor = BipartiteFlowGraph;


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

// The r-edges from sink->domain COULD in theory be re-used
function computeMaximalMatching(vars) {
    var source = new Vertex(null);
    var sink = new Vertex(null);

    var sunkenDomain = {};
    _.each(vars, function(rangeNode) {
        source.addAssignment(new Assignment(rangeNode));
        _.each(rangeNode.domain, function(domAssn) {
            var domNode = domAssn.to[0];
            if(!(domNode.id in sunkenDomain)) {
                var redge = new Assignment(domNode);
                sink.addAssignment(redge);
                sunkenDomain[domNode.id] = true; // TODO maybe add edges to a collection here for future pruning!
            }
        });
    });
    var flowGraph = new BipartiteFlowGraph(source, sink);

    var maxFlow = flowGraph.maxFlow(source, sink);
    console.log('flow: ' + flowGraph.maxFlow(source, sink));
    
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


// TODO conditionally add edges to matching

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
        /*
        for(var i=0; i<constraints.length; i++) {
            var cnst = constraints[i];
            var uniq = [];
            var affected = [];
            for(var t=0; t<cnst.to.length; t++) {
                if(!(cnst.to[t].id in uniq)) {
                    affected.push(cnst.to[t]);
                    uniq.push(cnst.to[t].id);
                }
            }
            Q.push([cnst, affected]);
        } */
        var arcs = _.map(constraints, function(cnst){
            return [cnst, _.unique(cnst.to.slice())] // PROBLEM, EXPANDING ABOVE
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
        for(var t=0; t<targetVar.domain.length; t++) { // TODO VERY IMPORTANT, HOW DID 'weight' GET ADDED TO THE ARRAY??????!!!!!!
            var targetVal = targetVar.domain[t].to[0]; // domain node
            if(cnst.check(pivotVal, targetVal)) { // is ordering preserved?
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


    // TEMPORARY
    var self = this;
    var vv = [];
    _.each(this.vMap, function(node){if(node instanceof Vertex) vv.push(node)});
    computeMaximalMatching(vv);
    // TEMPORARY

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
