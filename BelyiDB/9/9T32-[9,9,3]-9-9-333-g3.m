s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T32-[9,9,3]-9-9-333-g3";
s`BelyiDBFilename := "9T32-[9,9,3]-9-9-333-g3.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 9, 9, 3 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 3;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 9, 3, 2, 5, 4, 7, 6, 8, 1 ],
\[ 2, 4, 6, 3, 1, 7, 5, 8, 9 ],
\[ 1, 5, 6, 7, 2, 3, 4, 9, 8 ],
\[ 1, 4, 5, 6, 7, 2, 3, 8, 9 ]:
 Order := 1512 > |
[ 3, 4, 5, 7, 2, 9, 6, 1, 8 ],
[ 3, 7, 2, 9, 6, 4, 5, 1, 8 ],
[ 9, 7, 8, 3, 1, 2, 6, 4, 5 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 3, 4, 5, 7, 2, 9, 6, 1, 8 ],
\[ 3, 7, 2, 9, 6, 4, 5, 1, 8 ],
\[ 9, 7, 8, 3, 1, 2, 6, 4, 5 ]:
 Order := 1512 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 3, 4, 5, 7, 2, 9, 6, 1, 8 ],
\[ 3, 7, 2, 9, 6, 4, 5, 1, 8 ],
\[ 9, 7, 8, 3, 1, 2, 6, 4, 5 ]:
 Order := 1512 >) |
[ PermutationGroup<9 |  
\[ 3, 4, 5, 7, 2, 9, 6, 1, 8 ],
\[ 3, 7, 2, 9, 6, 4, 5, 1, 8 ],
\[ 9, 7, 8, 3, 1, 2, 6, 4, 5 ]:
 Order := 1512 > |
[ 3, 4, 5, 7, 2, 9, 6, 1, 8 ],
[ 3, 7, 2, 9, 6, 4, 5, 1, 8 ],
[ 9, 7, 8, 3, 1, 2, 6, 4, 5 ]
],
[ PermutationGroup<9 |  
\[ 3, 4, 5, 7, 2, 9, 6, 1, 8 ],
\[ 3, 7, 2, 9, 6, 4, 5, 1, 8 ],
\[ 9, 7, 8, 3, 1, 2, 6, 4, 5 ]:
 Order := 1512 > |
[ 5, 7, 2, 6, 4, 8, 9, 3, 1 ],
[ 5, 9, 6, 3, 4, 7, 8, 2, 1 ],
[ 2, 4, 7, 1, 9, 5, 8, 3, 6 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 9, 3, 2, 5, 4, 7, 6, 8, 1 ],
\[ 2, 4, 6, 3, 1, 7, 5, 8, 9 ],
\[ 1, 5, 6, 7, 2, 3, 4, 9, 8 ],
\[ 1, 4, 5, 6, 7, 2, 3, 8, 9 ]:
 Order := 1512 >) |
[ PermutationGroup<9 |  
\[ 9, 3, 2, 5, 4, 7, 6, 8, 1 ],
\[ 2, 4, 6, 3, 1, 7, 5, 8, 9 ],
\[ 1, 5, 6, 7, 2, 3, 4, 9, 8 ],
\[ 1, 4, 5, 6, 7, 2, 3, 8, 9 ]:
 Order := 1512 > |
[ 3, 4, 5, 7, 2, 9, 6, 1, 8 ],
[ 3, 7, 2, 9, 6, 4, 5, 1, 8 ],
[ 9, 7, 8, 3, 1, 2, 6, 4, 5 ]
],
[ PermutationGroup<9 |  
\[ 9, 3, 2, 5, 4, 7, 6, 8, 1 ],
\[ 2, 4, 6, 3, 1, 7, 5, 8, 9 ],
\[ 1, 5, 6, 7, 2, 3, 4, 9, 8 ],
\[ 1, 4, 5, 6, 7, 2, 3, 8, 9 ]:
 Order := 1512 > |
[ 6, 3, 8, 1, 7, 9, 2, 4, 5 ],
[ 6, 8, 5, 1, 2, 7, 9, 4, 3 ],
[ 8, 6, 5, 2, 7, 4, 3, 9, 1 ]
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
