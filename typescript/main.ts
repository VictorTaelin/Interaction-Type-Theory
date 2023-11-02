import * as itt from "./itt";
import * as lam from "./lam";

var term = lam.parse(`
let T   = λT.t λT.f T.t
let F   = λF.t λF.f F.f
let not = λnot.b (not.b F T)
let c0  = λc0.f λc0.x c0.x
let c1  = λc1.f λc1.x (c1.f c1.x)
let c2  = λc2.f λc2.x (c2.f (c2.f c2.x))
let k2  = λk2.f λk2.x (k2.f (k2.f k2.x))
let c3  = λc3.f λc3.x (c3.f (c3.f (c3.f c3.x)))
let c4  = λc4.f λc4.x (c4.f (c4.f (c4.f (c4.f c4.x))))
let c8  = λc8.f λc8.x (c8.f (c8.f (c8.f (c8.f (c8.f (c8.f (c8.f (c8.f c8.x))))))))
let c16 = λc16.f λc16.x (c16.f (c16.f (c16.f (c16.f (c16.f (c16.f (c16.f (c16.f (c16.f (c16.f (c16.f (c16.f (c16.f (c16.f (c16.f (c16.f c16.x))))))))))))))))
let c17 = λc17.f λc17.x (c17.f (c17.f (c17.f (c17.f (c17.f (c17.f (c17.f (c17.f (c17.f (c17.f (c17.f (c17.f (c17.f (c17.f (c17.f (c17.f (c17.f c17.x)))))))))))))))))
let c18 = λc18.f λc18.x (c18.f (c18.f (c18.f (c18.f (c18.f (c18.f (c18.f (c18.f (c18.f (c18.f (c18.f (c18.f (c18.f (c18.f (c18.f (c18.f (c18.f (c18.f c18.x))))))))))))))))))
(c18 c2 not T)
`);

console.log(lam.show(term));
var root = lam.to_net(term);
console.log(itt.show(root));
console.log("---");

var root = itt.normal(root);
console.log(itt.show(root));
console.log("---");

console.log(lam.show(lam.from_net(root)));
console.log(itt.REWRITES);
