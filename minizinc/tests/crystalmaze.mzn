include "globals.mzn";

enum Vertices = _(1..8);
enum Values = _(1..8);
enum Edges = _(1..17);
array[Edges, 1..2] of Vertices: edges;

edges = array2d(Edges, 1..2,
        [| to_enum(Vertices, 1), to_enum(Vertices, 2),
         | to_enum(Vertices, 1), to_enum(Vertices, 3),
         | to_enum(Vertices, 1), to_enum(Vertices, 4),
         | to_enum(Vertices, 1), to_enum(Vertices, 5),
         | to_enum(Vertices, 2), to_enum(Vertices, 4),
         | to_enum(Vertices, 2), to_enum(Vertices, 5),
         | to_enum(Vertices, 2), to_enum(Vertices, 6),
         | to_enum(Vertices, 3), to_enum(Vertices, 4),
         | to_enum(Vertices, 3), to_enum(Vertices, 7),
         | to_enum(Vertices, 4), to_enum(Vertices, 5),
         | to_enum(Vertices, 4), to_enum(Vertices, 7),
         | to_enum(Vertices, 4), to_enum(Vertices, 8),
         | to_enum(Vertices, 5), to_enum(Vertices, 6),
         | to_enum(Vertices, 5), to_enum(Vertices, 7),
         | to_enum(Vertices, 5), to_enum(Vertices, 8),
         | to_enum(Vertices, 6), to_enum(Vertices, 8),
         | to_enum(Vertices, 7), to_enum(Vertices, 8) |]);

array[Vertices] of var Values: xs;

constraint forall (e in Edges)(abs(xs[edges[e, 1]] - xs[edges[e, 2]]) > 1);
constraint alldifferent(xs);

solve satisfy;

output [join(" ", [show(x) | x in xs])];
