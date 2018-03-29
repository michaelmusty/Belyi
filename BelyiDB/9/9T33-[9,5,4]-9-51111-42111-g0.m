s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T33-[9,5,4]-9-51111-42111-g0";
s`BelyiDBFilename := "9T33-[9,5,4]-9-51111-42111-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 9, 5, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 4, 5, 2, 3, 6, 7, 8, 9, 1 ],
[ 1, 9, 3, 4, 5, 2, 6, 7, 8 ],
[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 4, 5, 2, 3, 6, 7, 8, 9, 1 ],
\[ 1, 9, 3, 4, 5, 2, 6, 7, 8 ],
\[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ]:
 Order := 181440 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 4, 5, 2, 3, 6, 7, 8, 9, 1 ],
\[ 1, 9, 3, 4, 5, 2, 6, 7, 8 ],
\[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ]:
 Order := 181440 >) |
[ PermutationGroup<9 |  
\[ 4, 5, 2, 3, 6, 7, 8, 9, 1 ],
\[ 1, 9, 3, 4, 5, 2, 6, 7, 8 ],
\[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ]:
 Order := 181440 > |
[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
[ 6, 2, 1, 3, 4, 5, 7, 8, 9 ],
[ 9, 3, 2, 4, 5, 6, 1, 7, 8 ]
],
[ PermutationGroup<9 |  
\[ 4, 5, 2, 3, 6, 7, 8, 9, 1 ],
\[ 1, 9, 3, 4, 5, 2, 6, 7, 8 ],
\[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ]:
 Order := 181440 > |
[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
[ 1, 9, 3, 4, 5, 2, 6, 7, 8 ],
[ 2, 1, 6, 3, 4, 5, 7, 8, 9 ]
],
[ PermutationGroup<9 |  
\[ 4, 5, 2, 3, 6, 7, 8, 9, 1 ],
\[ 1, 9, 3, 4, 5, 2, 6, 7, 8 ],
\[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ]:
 Order := 181440 > |
[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
[ 1, 9, 2, 4, 5, 6, 3, 7, 8 ],
[ 2, 1, 3, 7, 4, 5, 6, 8, 9 ]
],
[ PermutationGroup<9 |  
\[ 4, 5, 2, 3, 6, 7, 8, 9, 1 ],
\[ 1, 9, 3, 4, 5, 2, 6, 7, 8 ],
\[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ]:
 Order := 181440 > |
[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
[ 1, 9, 2, 3, 5, 6, 7, 4, 8 ],
[ 2, 1, 3, 4, 8, 5, 6, 7, 9 ]
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
[ 4, 5, 2, 3, 6, 7, 8, 9, 1 ],
[ 1, 9, 3, 4, 5, 2, 6, 7, 8 ],
[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ]
],
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 4, 1, 7, 3, 6, 9, 5, 2, 8 ],
[ 1, 2, 8, 4, 5, 7, 3, 9, 6 ],
[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ]
],
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 4, 1, 7, 3, 8, 5, 9, 2, 6 ],
[ 1, 2, 8, 4, 9, 6, 3, 5, 7 ],
[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ]
],
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 4, 1, 2, 9, 3, 5, 8, 6, 7 ],
[ 1, 2, 3, 5, 8, 6, 9, 7, 4 ],
[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ]
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
