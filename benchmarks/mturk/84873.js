// function roundFloatAndString(num1, num2) {
//   num1 = floatToFloat(parseFloat(num1));
//   num2 = stringToFloat(num2.toString());
//   return Math.round(num1 + num2); }
function floatToFloat(_float) {
  _float = parseFloat(_float);
  return _float; }
function stringToFloat(_string) {
  _string = parseFloat(_string);
  return _string; }

//@pbe (constraint (= (roundFloatAndString 21.6 32) 54))
