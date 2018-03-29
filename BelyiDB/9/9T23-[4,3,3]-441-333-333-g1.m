s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T23-[4,3,3]-441-333-333-g1";
s`BelyiDBFilename := "9T23-[4,3,3]-441-333-333-g1.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 4, 3, 3 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 8, 4, 5, 1, 6, 7, 3, 2, 9 ],
\[ 1, 2, 4, 5, 3, 8, 6, 7, 9 ]:
 Order := 216 > |
[ 1, 5, 4, 8, 9, 2, 3, 7, 6 ],
[ 5, 9, 1, 8, 3, 4, 2, 6, 7 ],
[ 3, 8, 9, 5, 7, 2, 4, 6, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 1, 5, 4, 8, 9, 2, 3, 7, 6 ],
\[ 5, 9, 1, 8, 3, 4, 2, 6, 7 ],
\[ 3, 8, 9, 5, 7, 2, 4, 6, 1 ]:
 Order := 216 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 1, 5, 4, 8, 9, 2, 3, 7, 6 ],
\[ 5, 9, 1, 8, 3, 4, 2, 6, 7 ],
\[ 3, 8, 9, 5, 7, 2, 4, 6, 1 ]:
 Order := 216 >) |
[ PermutationGroup<9 |  
\[ 1, 5, 4, 8, 9, 2, 3, 7, 6 ],
\[ 5, 9, 1, 8, 3, 4, 2, 6, 7 ],
\[ 3, 8, 9, 5, 7, 2, 4, 6, 1 ]:
 Order := 216 > |
[ 7, 1, 3, 6, 9, 5, 8, 2, 4 ],
[ 7, 3, 9, 8, 4, 1, 6, 5, 2 ],
[ 9, 4, 2, 3, 7, 5, 6, 1, 8 ]
],
[ PermutationGroup<9 |  
\[ 1, 5, 4, 8, 9, 2, 3, 7, 6 ],
\[ 5, 9, 1, 8, 3, 4, 2, 6, 7 ],
\[ 3, 8, 9, 5, 7, 2, 4, 6, 1 ]:
 Order := 216 > |
[ 7, 1, 3, 6, 9, 5, 8, 2, 4 ],
[ 9, 6, 1, 7, 4, 8, 5, 2, 3 ],
[ 8, 6, 9, 1, 2, 5, 3, 4, 7 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 8, 4, 5, 1, 6, 7, 3, 2, 9 ],
\[ 1, 2, 4, 5, 3, 8, 6, 7, 9 ]:
 Order := 216 >) |
[ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 8, 4, 5, 1, 6, 7, 3, 2, 9 ],
\[ 1, 2, 4, 5, 3, 8, 6, 7, 9 ]:
 Order := 216 > |
[ 1, 5, 4, 8, 9, 2, 3, 7, 6 ],
[ 5, 9, 1, 8, 3, 4, 2, 6, 7 ],
[ 3, 8, 9, 5, 7, 2, 4, 6, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 8, 4, 5, 1, 6, 7, 3, 2, 9 ],
\[ 1, 2, 4, 5, 3, 8, 6, 7, 9 ]:
 Order := 216 > |
[ 1, 7, 5, 2, 8, 3, 9, 6, 4 ],
[ 2, 6, 7, 5, 9, 1, 8, 3, 4 ],
[ 6, 9, 2, 5, 8, 7, 1, 4, 3 ]
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
