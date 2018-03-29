s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T25-[9,9,3]-9-9-333-g3";
s`BelyiDBFilename := "9T25-[9,9,3]-9-9-333-g3.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 9, 9, 3 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 3;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 1, 2, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 324 > |
[ 4, 3, 6, 8, 7, 9, 1, 2, 5 ],
[ 5, 4, 6, 7, 8, 2, 1, 9, 3 ],
[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 4, 3, 6, 8, 7, 9, 1, 2, 5 ],
\[ 5, 4, 6, 7, 8, 2, 1, 9, 3 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 324 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 4, 3, 6, 8, 7, 9, 1, 2, 5 ],
\[ 5, 4, 6, 7, 8, 2, 1, 9, 3 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 324 >) |
[ PermutationGroup<9 |  
\[ 4, 3, 6, 8, 7, 9, 1, 2, 5 ],
\[ 5, 4, 6, 7, 8, 2, 1, 9, 3 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 324 > |
[ 4, 3, 6, 8, 7, 9, 1, 2, 5 ],
[ 5, 3, 6, 7, 8, 9, 1, 2, 4 ],
[ 4, 5, 8, 7, 6, 2, 1, 9, 3 ]
],
[ PermutationGroup<9 |  
\[ 4, 3, 6, 8, 7, 9, 1, 2, 5 ],
\[ 5, 4, 6, 7, 8, 2, 1, 9, 3 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 324 > |
[ 4, 3, 6, 8, 7, 9, 1, 2, 5 ],
[ 4, 5, 8, 7, 6, 9, 2, 1, 3 ],
[ 4, 3, 7, 8, 6, 9, 2, 1, 5 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 1, 2, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 324 >) |
[ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 1, 2, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 324 > |
[ 4, 3, 6, 8, 7, 9, 1, 2, 5 ],
[ 5, 4, 6, 7, 8, 2, 1, 9, 3 ],
[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]
],
[ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 1, 2, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 324 > |
[ 4, 3, 8, 6, 7, 2, 1, 9, 5 ],
[ 5, 3, 8, 7, 6, 2, 1, 9, 4 ],
[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]
]
];

/*
Base Field Data
*/


/*
Belyi Maps
*/


/*
Powser Bases
*/


/*
Return for eval
*/

return s;
