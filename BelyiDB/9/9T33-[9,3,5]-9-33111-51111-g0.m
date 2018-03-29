s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T33-[9,3,5]-9-33111-51111-g0";
s`BelyiDBFilename := "9T33-[9,3,5]-9-33111-51111-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 9, 3, 5 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 3, 9, 2, 1, 4, 5, 6, 7, 8 ],
[ 2, 3, 1, 5, 6, 4, 7, 8, 9 ],
[ 6, 2, 3, 4, 5, 7, 8, 9, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 3, 9, 2, 1, 4, 5, 6, 7, 8 ],
\[ 2, 3, 1, 5, 6, 4, 7, 8, 9 ],
\[ 6, 2, 3, 4, 5, 7, 8, 9, 1 ]:
 Order := 181440 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 3, 9, 2, 1, 4, 5, 6, 7, 8 ],
\[ 2, 3, 1, 5, 6, 4, 7, 8, 9 ],
\[ 6, 2, 3, 4, 5, 7, 8, 9, 1 ]:
 Order := 181440 >) |
[ PermutationGroup<9 |  
\[ 3, 9, 2, 1, 4, 5, 6, 7, 8 ],
\[ 2, 3, 1, 5, 6, 4, 7, 8, 9 ],
\[ 6, 2, 3, 4, 5, 7, 8, 9, 1 ]:
 Order := 181440 > |
[ 9, 1, 2, 3, 4, 5, 6, 7, 8 ],
[ 8, 3, 4, 2, 5, 6, 7, 9, 1 ],
[ 4, 2, 3, 5, 6, 7, 1, 8, 9 ]
],
[ PermutationGroup<9 |  
\[ 3, 9, 2, 1, 4, 5, 6, 7, 8 ],
\[ 2, 3, 1, 5, 6, 4, 7, 8, 9 ],
\[ 6, 2, 3, 4, 5, 7, 8, 9, 1 ]:
 Order := 181440 > |
[ 9, 1, 2, 3, 4, 5, 6, 7, 8 ],
[ 1, 3, 4, 2, 5, 6, 8, 9, 7 ],
[ 4, 2, 3, 5, 6, 9, 7, 8, 1 ]
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
[ 3, 9, 2, 1, 4, 5, 6, 7, 8 ],
[ 2, 3, 1, 5, 6, 4, 7, 8, 9 ],
[ 6, 2, 3, 4, 5, 7, 8, 9, 1 ]
],
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 3, 9, 2, 7, 4, 5, 1, 6, 8 ],
[ 2, 3, 1, 5, 6, 4, 7, 8, 9 ],
[ 7, 2, 3, 4, 5, 8, 6, 9, 1 ]
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
