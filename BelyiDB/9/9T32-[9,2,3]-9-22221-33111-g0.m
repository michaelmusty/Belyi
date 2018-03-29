s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T32-[9,2,3]-9-22221-33111-g0";
s`BelyiDBFilename := "9T32-[9,2,3]-9-22221-33111-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 9, 2, 3 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 9, 3, 2, 5, 4, 7, 6, 8, 1 ],
\[ 2, 4, 6, 3, 1, 7, 5, 8, 9 ],
\[ 1, 5, 6, 7, 2, 3, 4, 9, 8 ],
\[ 1, 4, 5, 6, 7, 2, 3, 8, 9 ]:
 Order := 1512 > |
[ 3, 4, 2, 8, 9, 5, 6, 7, 1 ],
[ 7, 3, 2, 8, 9, 6, 1, 4, 5 ],
[ 5, 2, 7, 3, 6, 1, 4, 8, 9 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 3, 4, 2, 8, 9, 5, 6, 7, 1 ],
\[ 7, 3, 2, 8, 9, 6, 1, 4, 5 ],
\[ 5, 2, 7, 3, 6, 1, 4, 8, 9 ]:
 Order := 1512 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 3, 4, 2, 8, 9, 5, 6, 7, 1 ],
\[ 7, 3, 2, 8, 9, 6, 1, 4, 5 ],
\[ 5, 2, 7, 3, 6, 1, 4, 8, 9 ]:
 Order := 1512 >) |
[ PermutationGroup<9 |  
\[ 3, 4, 2, 8, 9, 5, 6, 7, 1 ],
\[ 7, 3, 2, 8, 9, 6, 1, 4, 5 ],
\[ 5, 2, 7, 3, 6, 1, 4, 8, 9 ]:
 Order := 1512 > |
[ 9, 3, 1, 2, 6, 7, 8, 4, 5 ],
[ 9, 4, 6, 2, 5, 3, 8, 7, 1 ],
[ 6, 2, 4, 7, 1, 5, 3, 8, 9 ]
],
[ PermutationGroup<9 |  
\[ 3, 4, 2, 8, 9, 5, 6, 7, 1 ],
\[ 7, 3, 2, 8, 9, 6, 1, 4, 5 ],
\[ 5, 2, 7, 3, 6, 1, 4, 8, 9 ]:
 Order := 1512 > |
[ 5, 1, 9, 3, 7, 8, 4, 2, 6 ],
[ 5, 8, 9, 4, 1, 7, 6, 2, 3 ],
[ 8, 2, 4, 6, 5, 3, 1, 7, 9 ]
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
[ 3, 4, 2, 8, 9, 5, 6, 7, 1 ],
[ 7, 3, 2, 8, 9, 6, 1, 4, 5 ],
[ 5, 2, 7, 3, 6, 1, 4, 8, 9 ]
],
[ PermutationGroup<9 |  
\[ 9, 3, 2, 5, 4, 7, 6, 8, 1 ],
\[ 2, 4, 6, 3, 1, 7, 5, 8, 9 ],
\[ 1, 5, 6, 7, 2, 3, 4, 9, 8 ],
\[ 1, 4, 5, 6, 7, 2, 3, 8, 9 ]:
 Order := 1512 > |
[ 9, 8, 2, 3, 1, 7, 4, 5, 6 ],
[ 9, 3, 2, 5, 4, 7, 6, 8, 1 ],
[ 4, 2, 5, 6, 8, 1, 7, 3, 9 ]
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
