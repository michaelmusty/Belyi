s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T33-[7,3,3]-711-333-33111-g0";
s`BelyiDBFilename := "9T33-[7,3,3]-711-333-33111-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 7, 3, 3 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 9, 5, 3, 4, 7, 8, 6, 1, 2 ],
[ 3, 8, 9, 7, 4, 2, 5, 6, 1 ],
[ 2, 3, 1, 5, 6, 4, 7, 8, 9 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 9, 5, 3, 4, 7, 8, 6, 1, 2 ],
\[ 3, 8, 9, 7, 4, 2, 5, 6, 1 ],
\[ 2, 3, 1, 5, 6, 4, 7, 8, 9 ]:
 Order := 181440 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 9, 5, 3, 4, 7, 8, 6, 1, 2 ],
\[ 3, 8, 9, 7, 4, 2, 5, 6, 1 ],
\[ 2, 3, 1, 5, 6, 4, 7, 8, 9 ]:
 Order := 181440 >) |
[ PermutationGroup<9 |  
\[ 9, 5, 3, 4, 7, 8, 6, 1, 2 ],
\[ 3, 8, 9, 7, 4, 2, 5, 6, 1 ],
\[ 2, 3, 1, 5, 6, 4, 7, 8, 9 ]:
 Order := 181440 > |
[ 2, 3, 4, 5, 6, 7, 1, 8, 9 ],
[ 5, 9, 2, 1, 4, 8, 6, 7, 3 ],
[ 8, 4, 3, 9, 5, 1, 7, 6, 2 ]
],
[ PermutationGroup<9 |  
\[ 9, 5, 3, 4, 7, 8, 6, 1, 2 ],
\[ 3, 8, 9, 7, 4, 2, 5, 6, 1 ],
\[ 2, 3, 1, 5, 6, 4, 7, 8, 9 ]:
 Order := 181440 > |
[ 2, 3, 4, 5, 6, 7, 1, 8, 9 ],
[ 9, 1, 7, 6, 4, 5, 8, 3, 2 ],
[ 3, 2, 9, 8, 5, 6, 4, 7, 1 ]
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
[ 9, 5, 3, 4, 7, 8, 6, 1, 2 ],
[ 3, 8, 9, 7, 4, 2, 5, 6, 1 ],
[ 2, 3, 1, 5, 6, 4, 7, 8, 9 ]
],
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 8, 2, 5, 4, 7, 1, 6, 9, 3 ],
[ 9, 6, 2, 7, 4, 3, 5, 1, 8 ],
[ 2, 3, 1, 5, 6, 4, 7, 8, 9 ]
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
