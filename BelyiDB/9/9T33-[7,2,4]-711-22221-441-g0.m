s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T33-[7,2,4]-711-22221-441-g0";
s`BelyiDBFilename := "9T33-[7,2,4]-711-22221-441-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 7, 2, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 6, 2, 1, 3, 5, 8, 4, 9, 7 ],
[ 7, 3, 2, 4, 6, 5, 1, 9, 8 ],
[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 6, 2, 1, 3, 5, 8, 4, 9, 7 ],
\[ 7, 3, 2, 4, 6, 5, 1, 9, 8 ],
\[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]:
 Order := 181440 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 6, 2, 1, 3, 5, 8, 4, 9, 7 ],
\[ 7, 3, 2, 4, 6, 5, 1, 9, 8 ],
\[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]:
 Order := 181440 >) |
[ PermutationGroup<9 |  
\[ 6, 2, 1, 3, 5, 8, 4, 9, 7 ],
\[ 7, 3, 2, 4, 6, 5, 1, 9, 8 ],
\[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]:
 Order := 181440 > |
[ 7, 1, 2, 3, 4, 5, 6, 8, 9 ],
[ 1, 9, 7, 8, 6, 5, 3, 4, 2 ],
[ 9, 7, 8, 6, 5, 3, 1, 4, 2 ]
],
[ PermutationGroup<9 |  
\[ 6, 2, 1, 3, 5, 8, 4, 9, 7 ],
\[ 7, 3, 2, 4, 6, 5, 1, 9, 8 ],
\[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]:
 Order := 181440 > |
[ 7, 1, 2, 3, 4, 5, 6, 8, 9 ],
[ 1, 6, 8, 5, 4, 2, 9, 3, 7 ],
[ 6, 8, 5, 4, 2, 9, 1, 3, 7 ]
],
[ PermutationGroup<9 |  
\[ 6, 2, 1, 3, 5, 8, 4, 9, 7 ],
\[ 7, 3, 2, 4, 6, 5, 1, 9, 8 ],
\[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]:
 Order := 181440 > |
[ 7, 1, 2, 3, 4, 5, 6, 8, 9 ],
[ 4, 2, 9, 1, 6, 5, 8, 7, 3 ],
[ 2, 9, 1, 6, 5, 8, 4, 7, 3 ]
],
[ PermutationGroup<9 |  
\[ 6, 2, 1, 3, 5, 8, 4, 9, 7 ],
\[ 7, 3, 2, 4, 6, 5, 1, 9, 8 ],
\[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]:
 Order := 181440 > |
[ 7, 1, 2, 3, 4, 5, 6, 8, 9 ],
[ 4, 9, 3, 1, 6, 5, 8, 7, 2 ],
[ 9, 3, 1, 6, 5, 8, 4, 7, 2 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 >) |
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 6, 2, 1, 3, 5, 8, 4, 9, 7 ],
[ 7, 3, 2, 4, 6, 5, 1, 9, 8 ],
[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]
],
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 6, 1, 3, 2, 5, 8, 4, 9, 7 ],
[ 7, 2, 4, 3, 6, 5, 1, 9, 8 ],
[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]
],
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 8, 2, 1, 3, 4, 6, 5, 9, 7 ],
[ 5, 3, 2, 4, 1, 7, 6, 9, 8 ],
[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]
],
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 3, 9, 6, 4, 5, 8, 2, 7, 1 ],
[ 4, 9, 7, 1, 6, 5, 3, 8, 2 ],
[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]
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
