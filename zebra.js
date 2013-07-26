/*
 *  Currently shrinking code-base and making it significatnly more efficient
 *  Experimented with comparing ALL_DIFF global/n-ary constraints,
 *  How I'm interested in exploring n-ary in general, possibly auto-conversion
 *  FIXME somehow, yellow ends up with MORE than five in the domain after reverting
 *  and if I remember running without inferences, components > 10 with unrelated variables
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

var INSTRUMENTATION = 0; // timing to find inefficiency
var INSTCOUNT = 0;


var GLOBAL = {};

//#############################################
/////// GRAPH DATA STRUCTURE /////////////////
//#############################################

var Vertex = function(info) {
    this.id = _generateID(); // HANDLE COLLISIONS
    this.info = info;
};
Vertex.prototype = {
    id: null,
    info: null,
}
var Variable = function(info) {
    Vertex.call(this, info);
    this.domain = [];
}
Variable.prototype = new Vertex();

var Value = function(info) {
    Vertex.call(this, info);
}
Value.prototype = new Vertex();


var Edge = function(from, to, capacity) {
    this.from = from || null;
    this.to = to || null;
    this.capacity = capacity || 1;
    this.id = _generateID();
};
Edge.prototype = {
    from: null,
    to: null,
    toString: function() {
                  var tail = '(' + ((!!this.from) ? (this.from.info !== null ? this.from.info : 'null') : '*') + ')';
                  var head = '(' + _.map(this.to, function(t){ return (t.info !== null ? t.info : 'null') }).join(', ') + ')';
                  return tail + ' -----> ' + head;
              }
}

var UNARY=1, BINARY=2, NARY=3;
var Constraint = function(type, relation, scope) {
    // TODO fix inheritence so that we can set edge here!
    this.id = _generateID(); // HANDLE COLLISIONS
    this.type = type;

    this.check = function() { 
        var params = Array.prototype.slice.call(arguments);
        return relation.apply(this, params);
    }
};
Constraint.prototype = new Edge();
Constraint.prototype.interLock = function() {
    var cnst = this;
    _.each(this.to, function(variable) {
        if(typeof variable.constraints === 'undefined')
            variable.constraints = [];

        if(!(cnst in variable.constraints)) 
            variable.constraints.push(cnst);
    });
}

var Assignment = function(from, valNode, capacity) {
    Edge.call(this, from, [valNode], capacity);
    this.id = _generateID(); // HANDLE COLLISIONS
};
Assignment.prototype = new Edge();

var Graph = function(v, e, d) {
    this.vertices = [];
    this.edges = [];
    this.adj = {};
    this.directed = d || false;

    var graph = this;
    _.each(v, function(node){ graph.addVertex(node);});
    _.each(e, function(edge){graph.addEdge(edge);});
}

Graph.prototype = {
    vertices: null,
    edges: null,
    adj: null,
    directed: false,
    addVertex: function(v) {
        if(this.vertices.indexOf(v) === -1) 
            this.vertices.push(v);
        //else console.log('addVertex: blocked vertex ' + v.info);
    },

    addEdge: function(e) {
        if(this.edges.indexOf(e) === -1) {
            this.edges.push(e);
            if(e.from) {
                if(e.from.id in this.adj)
                    this.adj[e.from.id].push(e);
                else this.adj[e.from.id] = [ e ];
            }
            /* THIS BROKE THE FLOW
            var self = this;
            var coll = e.from ? e.to.concat(e.from) : e.to;
            _.each(coll, function(node){
                if(typeof self.adj[node.id] === 'undefined')
                    self.adj[node.id] = [];
                self.adj[node.id].push(e);
            }); */
        } //else console.log('Ignoring duplicate edge: ' + e);
    },

    // FIXME partially implemented, NEVER used
    removeEdge: function(e) {
        if(this.edges.indexOf(e) !== -1) {
            this.edges = _.without(this.edges, e);
            if(e.from) this.adj[e.from.id] = _.without(this.adj[e.from.id], e);
            var self = this;
            _.chain(e.to)
                .map(function(t){return t.id})
                .each(function(id){ self.adj[id] = _.without(self.adj[id], e); });
        }
    }
}

var BipartiteFlowGraph = function(range, domain, source, reversedSink) {
    console.log('BFG called: ' + range.length + ' rangeNodes, '+domain.length+' domain');
    Graph.call(this);
    // Temporary, will combine graph objects using prototype pattern.  (Maybe)
    // TODO remove and consolidate
    this.vertices = [];
    this.edges = [];
    this.adj = {};

    this.source = source || new Vertex('source');
    this.sink = reversedSink || new Vertex('sink');
    this.range = range || [];
    this.domain= domain || [];
    this.flow = {};
    this.clean = []; // will house edges that should be removed later
    this.matching = [];

    // TODO change this to something universal or use adj?
    this.source.domain = [];
    this.sink.domain = []; 

    var initialize = function() {
        var flowGraph = this;
        _.each(this.range, function(variable) {
            var sourceLink = new Edge(flowGraph.source, [variable]);
            var redge = new Edge(variable, [flowGraph.source], 0);
            sourceLink.redge = redge;
            redge.redge = sourceLink;
            flowGraph.addEdge(sourceLink);
            flowGraph.addEdge(redge);
        });

        _.each(this.range, function(variable) {
            flowGraph.addVertex(variable); // When consolidated, this will be a duplicate step
            _.each(flowGraph.domain, function(value){
                flowGraph.addVertex(value);
                var assn = new Assignment(variable, value);
                var redge = new Edge(value, [variable], 0);
                assn.redge = redge;
                redge.redge = assn;
                flowGraph.addEdge(assn);
                flowGraph.addEdge(redge);
            });
        });

        _.each(this.domain, function(value){
            var sinkLink = new Edge(flowGraph.sink, [value], 0);
            var redge = new Edge(value, [flowGraph.sink]);
            sinkLink.redge = redge;
            redge.redge = sinkLink;
            flowGraph.addEdge(sinkLink);
            flowGraph.addEdge(redge);
        });
    }

    this.rebuild = function(vars) { 
        var flowGraph = this;

        this.flush();


        _.each(this.adj[this.source.id], function(sourceLink) {
            if(vars.indexOf(sourceLink.to[0]) !== -1)
                sourceLink.capacity = 1;
        });

        // Activate the pipes
        _.each(vars, function(variable) {
            _.each(flowGraph.adj[variable.id], function(assn) {
                if(assn instanceof Assignment && variable.domain.indexOf(assn) !== -1) {
                    assn.capacity = 1;
                    _.each(flowGraph.adj[assn.to[0].id], function(sinkLink){
                        if(sinkLink.to[0] === flowGraph.sink)
                            sinkLink.capacity = 1;
                    });
                }
            });
        });

        /*
        console.log('source has: '+this.adj[this.source.id].length);
        console.log('sink has: '+this.adj[this.sink.id].length);

        console.log('flowGraph has '+this.edges.length+' edges');
        //_.each(this.edges, function(e){console.log(''+e);});
        console.log('flowGraph has '+this.vertices.length+' vertices');
        console.log('flowGraph range: '+this.range.length);
        console.log('flowGraph domain: '+this.domain.length);
        */
    }

    this.addEdge = function(e) {
        //console.log('BPF addEdge:');
        BipartiteFlowGraph.prototype.addEdge.call(this, e);
        if(!e.from) console.error('Adding an undirected edge to flowGraph!');
        else if(e instanceof Assignment) {
            if(!e.from.domain) e.from.domain = [];
            if(e.from.domain.indexOf(e) === -1)  {
         //       console.log('Adding '+e+' to domain of '+e.from.info);
                e.from.domain.push(e);
            }
        }
    }

    this.addVertex = function(v) {
        BipartiteFlowGraph.prototype.addVertex.call(this, v);
        if(v instanceof Variable && this.range.indexOf(v) === -1)
            this.range.push(v);
        if(v instanceof Value && this.domain.indexOf(v) === -1)
            this.domain.push(v);
    }

    this.flush = function() { 
        var self = this;
        this.flow = this.flow || {};
        _.each(this.edges, function(edge) { 
            edge.capacity = 0;
            self.flow[edge.id] = 0;
        });
    };

    // FIXME
    // Gracefully degrade to bipartite with matching bidirectionality
    this.demote = function(vars) {
        this.flush();
        // Decomposition will only traverse edges with capacity
        _.each(this.matching, function(match){ match.redge.capacity = 1; });
        _.each(vars, function(variable){
            _.each(variable.domain, function(assn) { assn.capacity = 1; });
        });
        //_.each(this.edges, function(e){if(e.capacity > 0) count++; console.log('CAPACITY: '+e.capacity+' '+e);});
        //_.each(this.edges, function(e){ delete e.redge; });
        //debugger;
    };

    this.maxFlow = function(source, sink) {
        console.log('MAXFLOW function');
        var self = this;
        function capSort(a, b){
            return b.capacity-a.capacity;
        }
        function flowSort(){
            return self.flow[b.id]-self.flow[a.id];
        }
        
        this.edges.sort(capSort);
        //_.each(this.edges, function(e){console.log('CAPACITY: '+e.capacity+' '+e);});
        //debugger;
        this.matching = [];
        var path = this.findPath(source, sink, []);

        // path in form [{ edge: edge, res: residualFlow }, ...]
        while(path) {
            // I think this will work as a min function
            var minFlow = _.reduce(path, function(minFlow, step){
               return step.res < minFlow ? step.res : minFlow;
            }, Infinity);

            // Merge path flow into graph - this blocks when unit flow is capacity!
            _.each(path, function(step){
                self.flow[step.edge.id] += minFlow;
                self.flow[step.edge.redge.id] -= minFlow;
            });

            path = this.findPath(source, sink, []);
        }

        return _.chain(this.adj[source.id])
            .map(function(link){ return self.adj[link.to[0].id]; })
            .flatten(true) // shallow
            .filter(function(link){ return link.to[0].info !== self.sink.info && self.flow[link.id] > 0; })
            .map(function(matchingEdge){
                self.matching.push(matchingEdge);
                return self.flow[matchingEdge.id]; // side-effect!!!
            })
            .reduce(function(sum, f){ 
                return f > 0 ? f+sum : sum; }, 0)
            .value();
    };

    this.findPath = function (src, dst, path) {
        if(src === dst || src.id === dst.id) {
           // console.log('src == sink, returning path of length '+path.length); 
            return path;
        }

        //console.log('edj lookup: '+src.info+' id: '+src.id);
        var edj = this.adj[src.id];
        for(var i = 0; i < edj.length; i++) {
            var edge = edj[i];
            var residual = edge.capacity - this.flow[edge.id];  // Equivalent to edge weight

            var inPath = false;
            _.each(path, function(step){
                if(step.edge.id === edge.id)
                    inPath = true;
            });
            /*
            if(!inPath && residual > 0)
                console.log(''+edge +' with capacity: '+edge.capacity+' and flow: '+this.flow[edge.id]);
            */

            if(residual > 0 && !inPath) {
                var newPath = path.concat([{ edge: edge, res: residual }]);
                var result = this.findPath(edge.to[0], dst, newPath);
                if(result)
                    return result;
            } 
        }
    };

    initialize.call(this);
}
BipartiteFlowGraph.prototype = new Graph();
BipartiteFlowGraph.prototype.selectValue = function(rangeNode, domainNode) {
    var edge;
    var removed = [];

    _.each(this.adj[rangeNode.id], function(assn){
        if(assn instanceof Assignment) {
            if(rangeNode.domain.indexOf(assn) !== -1) {
                if(assn.to[0] === domainNode) {
                    assn.capacity = 1;
                    edge = assn;
                } else {
                    assn.capacity = 0;
                    removed.push(assn);
                }
            } else assn.capacity = 0;
        }
    });

    if(!edge) 
        throw "Could not find "+domainNode.info+" in the domain of "+rangeNode.info;

    console.log('REMOVING: '+removed.join(', '));

    rangeNode.domain = _.difference(rangeNode.domain, removed);

    if(rangeNode.domain.length !== 1) 
        throw "Could not select "+domainNode.info+" from the domain of "+rangeNode.info;

    //return  [{ variable: rangeNode, edges: removed }];
    return  removed; // changed standard inference form
}

var getConstraint = function(scope, rel, optional) {
    var type = (scope.length > 2 ? NARY : (scope.length < 2 ? UNARY : BINARY));
    var from = scope[0]; 

    var check;
    var opt = typeof optional;
    if(opt === 'undefined' || opt === 'function')
        check = rel;
    else
        check = optional instanceof Array ? rel.apply(null, optional) : rel.call(null, optional);


    // TODO fix inheritence, this should not happen in a builder function
    var to = type === UNARY ? [from] : scope.slice();
    var cnst = new Constraint(type, check, scope); // FIXME
    cnst.to = to;
    cnst.from = from;

    if(opt === 'function') cnst.global = optional;

    return cnst;
}


//#############################################
/////// UTILITY FUNCTIONS ////////////////////
//#############################################


// This function will be called in the context of the Bipartite Graph
BipartiteFlowGraph.prototype.getStrongComponents = function(vars) {
    var graph = this;

    var uglyHackMap = {}; // TODO remove this collection

    var dpfIndex = {};
    var dpfStack = [];
    var index = 0;

    var components = [];

    var vertz = vars.concat(this.domain); // We want a sub-graph
    /*
    var look = _.map(vertz, function(v){return v.info});
    console.log('LOOK: '+look);
    */

    for(var idx in vertz) {
        var v = vertz[idx];
        if(!(v.id in dpfIndex))
            strongConnect(v)
    }
    
    function strongConnect(v) {
        var statV = {};
        statV.index = index;
        statV.lowlink = index++;
        dpfIndex[v.id] = statV;
        if(!uglyHackMap[v.id]) uglyHackMap[v.id] = v; // TODO move into graph
        dpfStack.push(v.id); // TODO I may be able to just push the vertex directly

        _.each(graph.adj[v.id], function(edge) {
            if(edge.capacity === 1) { // traversable
                //console.log('WALKING ACROSS: '+edge);
                var w = edge.to[0]; // successor node
                if(!(w.id in dpfIndex)) {
                    strongConnect(w);
                    statV.lowlink = Math.min(statV.lowlink, dpfIndex[w.id].lowlink);
                } else if(dpfStack.indexOf(w.id) !== -1) // the domain node is in the stack, which means it's in the current SCC
                    statV.lowlink = Math.min(statV.lowlink, dpfIndex[w.id].index);
            }
        });

        // if v is a root node, pop the stack and generate a component
        if(statV.lowlink === statV.index) {
            var scc = [];
            do {
                var p = dpfStack.pop(); // id of previously pushed node
                //scc.push(uglyHackMap[p].info); // FIXME
                scc.push(p); // FIXME
            } while(p !== v.id);
            components.push(scc);
        }
    }

    return components;
}

function _generateID () {
      var S4 = function() {
         return (((1+Math.random())*0x10000)|0).toString(16).substring(1);
      };
      return (S4()+S4()+"-"+S4()+"-"+S4()+"-"+S4()+"-"+S4()+S4()+S4());
}

function sortQ(a, b) {
    if(!a || !b) return 0;
    return a.type - b.type;
}

function isInDomain(rangeNode, valNode) {
    if(!rangeNode)
        throw "Problem during domain check";
    return _.some(rangeNode.domain, function(assn){
        return assn.to[0] === valNode;
    });
}

/* The function below has changed so that now we are just appending constraints, NOT arcs
 * The logic was ruined by earlier changes, so that members was always an empty set.
 * LOGIC:
 * We want to push all constraints for each node affected by the previous changes.
 * In the binary case, we have modified only one domain, that of the first in to. (pivot?)
 * In the nary case, we may have modified ANY of the constraints, and so we need to push all related for each
 * There is no notion of a pivot in the NARY case
 */
function queueAffectedNodes(Q, affected, justChecked) {
    if(affected.length > 0) {
        // for each in group (I will remove - previously - in the binary case as pivot is not modified)
        _.each(affected, function(vertex){
            var unnecessary = Q.concat(justChecked);
            var goingToPush = _.difference(vertex.constraints, unnecessary);
            if(goingToPush.length > 0) 
                Q.push.apply(goingToPush);
        });
    }
    Q.sort(sortQ);
    var displayQ = _.map(Q, function(q){return '\n'+parseInt(q.type) + q.toString()}); // maybe will look ok?
    console.log('\n\ndisplayQ: '+displayQ);
}

// Q will always be empty before performing the three additions.  
function initializeQueue(constraints, Q) {
    if(Q instanceof Array)  {
        var arcs = _.difference(constraints, Q);
        if(arcs.length > 0) {
            Q.push.apply(Q, constraints);
        }
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

    var ALL_DIFF_STUPID = function(vars, passed) {
        function isAssigned(v) {
            return v.domain.length === 1;
        }
        

        var assigned = _.filter(vars, isAssigned);
        if(assigned.length === vars.length) {
            var allDiff = _.chain(vars).map(function(v){ return v.domain[0].to[0].info }).unique().value().length === vars.length;
            return allDiff;
        } else return true;
    }

    var ALL_DIFF_SIMPLE = function(vars, passed) {

        function isAssigned(v) {
            return v.domain.length === 1;
        }
        //var start = Date.now();

        var assigned = _.filter(vars, isAssigned);
        if(assigned.length === vars.length) {
            var allDiff = _.chain(vars).map(function(v){ return v.domain[0].to[0].info }).unique().value().length === vars.length;
                    //var end = Date.now();
                    //INSTRUMENTATION += (end-start);
                    //INSTCOUNT++;
            return allDiff;
        } else { // not all assigned
            var unassigned = _.reject(vars, isAssigned); 
            var domainColl = _.chain(unassigned).map(function(v){ return v.domain }).value();
            var domains = [];
            _.each(domainColl, function(edges){
                var flatVals = _.map(edges, function(domEdge){ return domEdge.to[0].info; });
                domains.push(flatVals);
            });
            // at least one
            var num = domains[0].length;
            var allSame = _.every(domains, function(dom){ return dom.length === num; });
            if(allSame) {
                    //var end = Date.now();
                    //INSTRUMENTATION += (end-start);
                    //INSTCOUNT++;
                if(num < unassigned.length) return false; // will result in empty domain
                else return true; // possible
            } else { // Hook for revision override here
                return true; 
            }
        }
    }

    /* The general strategy for my ALL-DIFF is as follows:
     * Construct Bipartite Graph
     * Use flow theory to fail early on sub-perfect maximal
     * Use Hopcroft-Karp to find perfect matching 
     * Decompose graph into strongly connected components
     * Prune edges by removing component-bridges
    **/
    // IMPORTANT:
    // Return true if we want to revise, false if we want to skip revision, and FAILURE if we fail the constraint
    var ALL_DIFF = function(vars, passed) {
        console.log('vars length: '+vars.length);

        passed.push(vars); // We will use these in our revision function to limit the component graph

        /*
         * I will now use the closure nature of this method to share the domain graph between iterations
         */
        INSTRUMENTATION += 1; // lol
        INSTCOUNT++;

        // ALL_DIFF_STUPID inclusion to avoid checking in the straightforward cases
        function isAssigned(v) {
            return v.domain.length === 1;
        }
        

        var assigned = _.filter(vars, isAssigned);
        if(assigned.length === vars.length) {
            var allDiff = _.chain(vars).map(function(v){ return v.domain[0].to[0].info }).unique().value().length === vars.length;
            console.log('RETURING BYPASS!!!');
            return allDiff ? false : FAILURE; // false means we skip the revision step
        } else {

        // Not all assigned: original function continues below

        this.domainGraph.rebuild(vars);

        //var start = Date.now();
        var maxFlow = this.domainGraph.maxFlow(this.domainGraph.source, this.domainGraph.sink);  // TODO add wrapper function to graph
        if(maxFlow === vars.length) console.log('GOOD');
        //console.log('MAX flow: ' + maxFlow);

        this.domainGraph.demote(vars); // safely cleans and prepares the graph state
        //var end = Date.now();

        // TODO HANDLE k-regular, where we should return false instead of true for efficiency
        return (maxFlow == vars.length) || FAILURE; // perfect matching exists

        }
    }


    GLOBAL['ALLDIFF_REVISE'] = function(vars, inferences) {
        if(!this.domainGraph || !inferences) {
            console.error('MAJOR PROBLEM, GLOBAL CLOSURE NOT WORKING');
            return [];
        }

        //var start = Date.now();
        var components = this.domainGraph.getStrongComponents(vars); 
        console.log('components size: '+components.length);

        /*
        var csp = this;
        var displayComp = [];
        _.each(components, function(cmp){
            var dsp = [];
            _.each(cmp, function(id){
                _.each(csp.graph.vertices, function(vert){
                    if(vert.id === id)
                        dsp.push(vert.info);
                });
            });
            displayComp.push(dsp);
        });
        console.log('\n');
        console.log(displayComp);
        console.log('\n');
        */

        if(components.length > 9) {
            console.log(components);
            throw 'what';
        }
        //var end = Date.now();
        //INSTRUMENTATION += (end-start);
        //INSTCOUNT++;

        var dedges =  _.chain(vars)
            .map(function(variable){ return variable.domain; })
            .flatten(true).value();
        
        var notInMatching = _.difference(dedges, this.domainGraph.matching);

        var inf = _.chain(notInMatching)
            .map(function(match) {

                var comp;
                for(var x in components)
                    if(components[x].indexOf(match.from.id) != -1)
                        comp = components[x];

                var deadEnd = [];
                if(comp && comp.indexOf(match.to[0].id) === -1) {

                    console.log('SAFE TO REMOVE EDGE: ' + match);
                    match.from.domain = match.from.domain = _.without(match.from.domain, match);
                    deadEnd.push(match);
                    return match;

                } else return undefined;
            }).compact().value();
        

        inferences.push.apply(inferences, inf);

        return inf.length > 0; // modified?
    }

//#############################################
////////// ALT. CONSISTENCY ALGORITHMS  //////
//#############################################


function ac3(csp, inferences) {
    var Q = []; 
    initializeQueue(csp.cMap[UNARY], Q);
    initializeQueue(csp.cMap[BINARY], Q);
    initializeQueue(csp.cMap[NARY], Q);
    
    while(Q.length > 0) {
        var cnst = Q.shift();
        if(typeof cnst === undefined) { // FIXME avoid pushing undefined arcs
            console.error('UNDEFINED ARC IN QUEUE!!!!');
            continue; 
        }

        switch(parseInt(cnst.type)){
            case UNARY:
            case BINARY:
                if(csp.revise(cnst, inferences, cnst.to)) {
                    if(cnst.to[0].domain.length === 0)  
                        return FAILURE; 

                    // First argument passes in only one vertex 
                    // because algorith leaves the second untouched
                    queueAffectedNodes(Q, [cnst.to[0]], cnst); 
                }
                break;
            case NARY:
                    var reviseParams = [];
                    console.log('CALLING ALL_DIFF: '+cnst);
                    var result = cnst.check.call(csp, cnst.to, reviseParams); // TODO ensure that this is the same statement as the BINARY/UNARY case (use a cycle if I have to)
                if(result === true) {
                    if(cnst.global) { // constraint has a revision override
                        // We must pass inferences long to be modified
                        reviseParams.push(inferences); 
                        //var start = Date.now();
                        var modified = cnst.global.apply(csp, reviseParams); // Constraints are applied in the context of the CSP now
                        //var end = Date.now();
                        //INSTRUMENTATION+=(end-start);
                        //INSTCOUNT++;
                        if(modified) {
                            var broken = _.some(cnst.to, function(affected){ return affected.domain.length === 0 });
                            if(broken) 
                                return FAILURE;
                            else 
                                queueAffectedNodes(Q, cnst.to, cnst);
                        } 
                    }// else console.warn('Constraint WILL NOT revise, nary currently requires revision override!');
                } else if(result === FAILURE) 
                    return FAILURE; // failed the constraint
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
  
// TODO clean this up, removed unnecessary constructs
var csp = function(variables, domain, constraints) {
    var self = this;
    this.stats = { depth: 0, max: 0, inf: 0, backtracks: 0, time: null};
    this.domain = _.map(domain, function(val){return new Value(val);});
    this.range = [];
    this.vMap = {}; // ONLY WORKS WITH STRINGS / UUIDS!!!
    this.numVars = variables.length;

    _.each(variables, function(v){
        var vrb = new Variable(v);
        self.vMap[v] = vrb;
        self.range.push(vrb);
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

    // before building, we want all variables in vMap
    this.buildConstraintGraph();

    // TODO eliminate vMap
    this.domainGraph = new BipartiteFlowGraph(this.range, this.domain);
}



csp.prototype.solve = function() {
    var assignment = {}; 
    _.each(this.vMap, function(node){assignment[node.info]=node});

    var start = Date.now();
    var solution = this.backTrack(assignment);
    this.stats.time = (Date.now() - start);

    function printStats(solved){
        var hdr = !solved ? '\n\nNot solved... ' : '\n\nSolved in ' +
                (this.stats.time < 1000 ? this.stats.time+" ms" : this.stats.time/1000+" seconds") + "!";
        console.log(hdr +
                "\ndepth: "+this.stats.depth +
                "\nmax depth: "+this.stats.max +
                "\ninferences: "+this.stats.inf +
                "\nbacktracks: "+this.stats.backtracks+"\n\n\n");
    }

    if(solution !== FAILURE) {
        printStats.call(this, true);
        if(INSTRUMENTATION > 0) 
            console.log('Instrumentation time: '+INSTRUMENTATION + '\n(ran '+INSTCOUNT+' times)');

        //console.log(solution);
        printSolution.call(this, solution);
    } else {
        printStats.call(this, false);
        console.log("Failed to find a solution");
    }
}

function printSolution(sol) {
    var per=0,pet=1,col=2,drnk=3,cand=4;

    for(var v in this.graph.vertices) 
        console.log('\n NOASSIGNMENTCHECK '+this.graph.vertices[v].info);

    var houses = new Array(5);
    houses[per] = new Array(5);
    houses[pet] = new Array(5);
    houses[col] = new Array(5);
    houses[drnk] = new Array(5);
    houses[cand] = new Array(5);

    for(var i=0; i<5; i++) {
        for(var v in sol) {
            var solvDomain = this.graph.adj[sol[v].id];
            for(var d in solvDomain) {
                if(!solvDomain[d].to)
                    continue;
                else {
                    var varName = sol[v].info;
                    var houseNum = solvDomain[d].to[0].info-1;
                    console.log('info: '+solvDomain[d].to[0].info);
                    console.log('houseNum '+houseNum);
                    if(people.indexOf(varName) !== -1)
                        houses[houseNum][per] = varName;
                    else if(pets.indexOf(sol[v].info) !== -1)
                        houses[houseNum][pet] = varName;
                    else if(colors.indexOf(sol[v].info) !== -1)
                        houses[houseNum][col] = varName;
                    else if(drinks.indexOf(sol[v].info) !== -1)
                        houses[houseNum][drnk] = varName;
                    else if(candies.indexOf(sol[v].info) !== -1)
                        houses[houseNum][cand] = varName;
                }
            }
        }
    }

    function pretty(slot) {
        return slot + (k==4 ? '\n' : 
            ((slot.length < 8) ? '\t\t' : '\t'));
    }

    var hstr = ''
    for(var i=0; i<5; i++)  {
        for(var k=0; k<5; k++) {
            hstr += pretty(houses[k][i]);
           // hstr += houses[per][i] + sp + houses[pet][i] + sp + houses[col][i] + sp +  houses[drnk][i] + sp + houses[cand][i] + '\n'; 
        }
    }
    console.log(hstr);
}

// I believe this can easily be generalized to n-ary
// However, it would be very inefficient for some constraints.
// For this reason, I'm including a 'global' function in the definition
// of a constraint which will allow me to override this logic
csp.prototype.revise = function(cnst, inferences, params) {
    var pivotVar = params[0];
    var modified = false;
    // if no value for v2 exists in C(v1,v2), remove v1 from domaim
    var removed = [];
    _.each(pivotVar.domain, function(assnEdge){
        var found=false;
        var pivotVal = assnEdge.to[0];
        var targetVar = parseInt(cnst.type) === UNARY ? pivotVar : params[1]; // UGLY unary case
        for(var t=0; t<targetVar.domain.length; t++) { 
            var targetVal = targetVar.domain[t].to[0]; // domain node
            if(cnst.check(pivotVal, targetVal)) { 
                found = true;
                break;
            }
        }
        if(!found) {
            pivotVar.domain = _.without(pivotVar.domain, assnEdge);
            removed.push(assnEdge); // TODO remove, just for logging
            inferences.push(assnEdge);
            modified = true;
        }
    });
    if(modified) {
        console.log('\nValues removed by constriant: '+cnst);
        console.log(removed.join('\n'));
    }
    return modified;
}

csp.prototype.revert = function(inferences) {
    this.stats.backtracks++;
    //console.log('REVERTING');
    if(!inferences) return;
    var need = inferences.length;
    var cnt = 0;
    while(inferences.length > 0) {
        cnt++;
        var goodEdge = inferences.pop();
        goodEdge.from.domain.push(goodEdge);
    }
    if(cnt !== need) throw 'PROBABLY DIDN\'T REVERT ERROR';
}

// We want the variable with the smallest remaining domain
// that has the most constraints
csp.prototype.getMostConstrainedVar = function() {
    function varSort(a,b) {
        if(a.domain.length < b.domain.length)
            return -1;
        else if(a.domain.length > b.domain.length)
            return 1;
        else if(a.domain.length === b.domain.length)
            return b.constraints.length - a.constraints.length;
    }

    //var dL = _.map(this.graph.vertices, function(v){return v.info}).join('/');
    //console.log('UNSORTED DOMAIN LENGTHS: '+dL);
    this.graph.vertices.sort(varSort);
    //dL = _.map(this.graph.vertices, function(v){return v.info}).join('/');
    //console.log('SORTED DOMAIN LENGTHS: '+dL);
    for(var i=0; i<this.graph.vertices.length; i++) {
        var variable = this.graph.vertices[i];
        if( variable.domain.length > 1 ) return variable; // presorted
    }
    /*
    var most = null;
    for(var i=0; i<this.graph.vertices.length; i++) {
        var variable = this.graph.vertices[i];
        console.log('sort find: ' + variable.info + '\ndomain: '+variable.domain.length);
        if( !most || variable.domain.length > most.domain.length) most = variable;
    }
    return most;
    */
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

    if(!considered) return assignment;

    var inferences;
    // If we want to choose least constraining, we have to infer for every value first!!!
    for(var vn=0; vn<this.domain.length; vn++) {
        var valNode = this.domain[vn];
        if(isInDomain(considered, valNode)) {
            console.log('Trying ' + considered.info + ' : ' + valNode.info);
            if(considered.info === 'yellow' && valNode.info === 5)
                debugger;
            inferences = this.domainGraph.selectValue(considered, valNode);
            var ret = this.infer(inferences);
            if(ret !== FAILURE) { 
                console.log('RECURSING');
                var recur = this.backTrack(assignment);
                if(recur !== FAILURE)
                    return recur;
            } else {
                this.stats.backtracks++;
                this.stats.depth = 0;
            }
        } //else console.log('Could not select '+valNode.info +' from domain of length '+considered.domain.length);
        var d = _.map(inferences, function(ii){return ii.from.info + ' ' + ii.to[0].info}).join(', ');
        console.log('Reverting: \n'+d);
        // completely revert
        this.revert(inferences); // adds the edges back into the graph
        var problem = _.filter(this.graph.vertices, function(vv){return vv.domain.length !== 5});
        var ylw = (_.map(problem, function(p){return p.info}));
        var ylwd = (_.map(problem, function(p){return p.domain}));
//        if(problem.length > 0) console.log('HERE BE DRAGONS: ' + ylw + ' : ' + ylwd);
    }
    return FAILURE;
}

csp.prototype.infer = function(inferences) {
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
    _.each(this.vMap, function(varNode){ vertices.push(varNode); });

    var graph = new Graph(vertices);

    // TODO rework this method
    for(var type in this.cMap){
        switch(parseInt(type)) {
            case UNARY: // no cycles, need only apply once
                break;
            case BINARY:
            case NARY:
                // for each constraint
                _.each(this.cMap[type], function(cc){
                    // for each node affected by it
                    _.each(cc.to, function(vertex){
                        graph.addEdge(cc);
                        cc.interLock();
                    });
                });
                break;
            default:
                break;
        }
    }

    this.graph = graph;
}

// If function is passed, it will be a global revision function.
// The revision argument will receive the extra parameter to check
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
    [ ["milk"], VALUE, [3]],
    /*
    [ people, ALL_DIFF ],
    [ pets, ALL_DIFF ],
    [ colors, ALL_DIFF ],
    [ drinks, ALL_DIFF ],
    [ candies, ALL_DIFF ]
     */
    [ people, ALL_DIFF, GLOBAL['ALLDIFF_REVISE'] ],
    [ pets, ALL_DIFF, GLOBAL['ALLDIFF_REVISE'] ],
    [ colors, ALL_DIFF, GLOBAL['ALLDIFF_REVISE'] ],
    [ drinks, ALL_DIFF, GLOBAL['ALLDIFF_REVISE'] ],
    [ candies, ALL_DIFF, GLOBAL['ALLDIFF_REVISE'] ]
];

var problem = new csp(variables, domain, constraints);
problem.solve();
