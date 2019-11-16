function myFunction( var ) {
 return var; }

myFunction( value ); var myObject = {
 var : value, functionName: function () {
 return this.var; }
}
myObject.functionName(); 

function addStuff(args) {
 return args + 2; }

addStuff(2); //returns 4 //arrow function var addStuff = (args) => args + 2; addStuff(2); //returns 4
