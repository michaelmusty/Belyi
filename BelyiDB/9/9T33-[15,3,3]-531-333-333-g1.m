s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T33-[15,3,3]-531-333-333-g1";
s`BelyiDBFilename := "9T33-[15,3,3]-531-333-333-g1.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 15, 3, 3 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 5, 2, 9, 8, 3, 4, 1, 6, 7 ],
[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
[ 9, 1, 4, 5, 3, 7, 8, 6, 2 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 5, 2, 9, 8, 3, 4, 1, 6, 7 ],
\[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
\[ 9, 1, 4, 5, 3, 7, 8, 6, 2 ]:
 Order := 181440 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 5, 2, 9, 8, 3, 4, 1, 6, 7 ],
\[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
\[ 9, 1, 4, 5, 3, 7, 8, 6, 2 ]:
 Order := 181440 >) |
[ PermutationGroup<9 |  
\[ 5, 2, 9, 8, 3, 4, 1, 6, 7 ],
\[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
\[ 9, 1, 4, 5, 3, 7, 8, 6, 2 ]:
 Order := 181440 > |
[ 2, 3, 4, 5, 1, 7, 8, 6, 9 ],
[ 9, 7, 1, 5, 6, 4, 8, 2, 3 ],
[ 4, 3, 8, 9, 6, 7, 5, 2, 1 ]
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
[ 5, 2, 9, 8, 3, 4, 1, 6, 7 ],
[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
[ 9, 1, 4, 5, 3, 7, 8, 6, 2 ]
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
