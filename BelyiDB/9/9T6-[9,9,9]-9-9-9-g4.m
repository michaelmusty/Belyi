s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T6-[9,9,9]-9-9-9-g4";
s`BelyiDBFilename := "9T6-[9,9,9]-9-9-9-g4.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 9, 9, 9 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 4;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 4, 8, 3, 7, 2, 6, 1, 5, 9 ],
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ]:
 Order := 27 > |
[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
[ 2, 6, 1, 5, 9, 4, 8, 3, 7 ],
[ 5, 3, 1, 8, 6, 4, 2, 9, 7 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |  
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 3 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |  
\[ 7, 8, 9, 1, 2, 3, 4, 5, 6 ]:
 Order := 3 >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 6, 1, 5, 9, 4, 8, 3, 7 ],
\[ 5, 3, 1, 8, 6, 4, 2, 9, 7 ]:
 Order := 27 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 6, 1, 5, 9, 4, 8, 3, 7 ],
\[ 5, 3, 1, 8, 6, 4, 2, 9, 7 ]:
 Order := 27 >) |
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 6, 1, 5, 9, 4, 8, 3, 7 ],
\[ 5, 3, 1, 8, 6, 4, 2, 9, 7 ]:
 Order := 27 > |
[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
[ 2, 9, 7, 5, 3, 1, 8, 6, 4 ],
[ 2, 6, 1, 5, 9, 4, 8, 3, 7 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 6, 1, 5, 9, 4, 8, 3, 7 ],
\[ 5, 3, 1, 8, 6, 4, 2, 9, 7 ]:
 Order := 27 > |
[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
[ 2, 6, 1, 5, 9, 4, 8, 3, 7 ],
[ 5, 3, 1, 8, 6, 4, 2, 9, 7 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 4, 8, 3, 7, 2, 6, 1, 5, 9 ],
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ]:
 Order := 27 >) |
[ PermutationGroup<9 |  
\[ 4, 8, 3, 7, 2, 6, 1, 5, 9 ],
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ]:
 Order := 27 > |
[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
[ 2, 6, 1, 5, 9, 4, 8, 3, 7 ],
[ 5, 3, 1, 8, 6, 4, 2, 9, 7 ]
],
[ PermutationGroup<9 |  
\[ 4, 8, 3, 7, 2, 6, 1, 5, 9 ],
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ]:
 Order := 27 > |
[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
[ 2, 9, 7, 5, 3, 1, 8, 6, 4 ],
[ 2, 6, 1, 5, 9, 4, 8, 3, 7 ]
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
