s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T33-[7,3,3]-711-333-333-g1";
s`BelyiDBFilename := "9T33-[7,3,3]-711-333-333-g1.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 7, 3, 3 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 8, 3, 6, 4, 2, 9, 7, 5, 1 ],
[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
[ 8, 4, 1, 6, 7, 2, 9, 3, 5 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 8, 3, 6, 4, 2, 9, 7, 5, 1 ],
\[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
\[ 8, 4, 1, 6, 7, 2, 9, 3, 5 ]:
 Order := 181440 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 8, 3, 6, 4, 2, 9, 7, 5, 1 ],
\[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
\[ 8, 4, 1, 6, 7, 2, 9, 3, 5 ]:
 Order := 181440 >) |
[ PermutationGroup<9 |  
\[ 8, 3, 6, 4, 2, 9, 7, 5, 1 ],
\[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
\[ 8, 4, 1, 6, 7, 2, 9, 3, 5 ]:
 Order := 181440 > |
[ 2, 3, 4, 5, 6, 7, 1, 8, 9 ],
[ 4, 7, 6, 5, 1, 8, 9, 3, 2 ],
[ 2, 5, 9, 8, 1, 4, 3, 6, 7 ]
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
[ 8, 3, 6, 4, 2, 9, 7, 5, 1 ],
[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
[ 8, 4, 1, 6, 7, 2, 9, 3, 5 ]
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
