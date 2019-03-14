const repl = require('repl');
const fs = require('fs');

const rep = repl.start({ prompt: '', eval: myEval });

function makeEvalContext (declarations)
{
    eval(declarations);
    return function (str) { return eval(str); }
}

var ev = makeEvalContext ("");

// Based on https://stackoverflow.com/questions/9781285/specify-scope-for-eval-in-javascript
function myEval(cmd, context, filename, callback) {
    var cmd_split = cmd.replace("\n", "").split(" ")
    if (cmd_split[0] === "LOAD") {
        fs.readFile(cmd_split[1], "utf8", function(err, data) { 
            ev = makeEvalContext(data);
            callback(null, "LOADED " + cmd_split[1]);
        });
        
    }
    else {
        r = ev(cmd);
        callback(null, r);
    }
}