s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T11-[6,6,3]-621-621-333-g1";
s`BelyiDBFilename := "9T11-[6,6,3]-621-621-333-g1.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 6, 6, 3 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 1, 2, 4, 5, 3, 8, 6, 7, 9 ],
\[ 2, 1, 6, 8, 7, 3, 5, 4, 9 ]:
 Order := 54 > |
[ 5, 4, 2, 1, 9, 7, 6, 8, 3 ],
[ 7, 6, 4, 3, 5, 9, 2, 1, 8 ],
[ 3, 4, 6, 7, 8, 1, 2, 9, 5 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 5, 4, 2, 1, 9, 7, 6, 8, 3 ],
\[ 7, 6, 4, 3, 5, 9, 2, 1, 8 ],
\[ 3, 4, 6, 7, 8, 1, 2, 9, 5 ]:
 Order := 54 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 5, 4, 2, 1, 9, 7, 6, 8, 3 ],
\[ 7, 6, 4, 3, 5, 9, 2, 1, 8 ],
\[ 3, 4, 6, 7, 8, 1, 2, 9, 5 ]:
 Order := 54 >) |
[ PermutationGroup<9 |  
\[ 5, 4, 2, 1, 9, 7, 6, 8, 3 ],
\[ 7, 6, 4, 3, 5, 9, 2, 1, 8 ],
\[ 3, 4, 6, 7, 8, 1, 2, 9, 5 ]:
 Order := 54 > |
[ 5, 4, 2, 1, 9, 7, 6, 8, 3 ],
[ 2, 1, 8, 7, 6, 4, 3, 5, 9 ],
[ 6, 7, 9, 1, 2, 4, 5, 3, 8 ]
],
[ PermutationGroup<9 |  
\[ 5, 4, 2, 1, 9, 7, 6, 8, 3 ],
\[ 7, 6, 4, 3, 5, 9, 2, 1, 8 ],
\[ 3, 4, 6, 7, 8, 1, 2, 9, 5 ]:
 Order := 54 > |
[ 5, 4, 2, 1, 9, 7, 6, 8, 3 ],
[ 2, 1, 7, 6, 8, 5, 4, 3, 9 ],
[ 7, 8, 9, 1, 2, 3, 4, 5, 6 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 1, 2, 4, 5, 3, 8, 6, 7, 9 ],
\[ 2, 1, 6, 8, 7, 3, 5, 4, 9 ]:
 Order := 54 >) |
[ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 1, 2, 4, 5, 3, 8, 6, 7, 9 ],
\[ 2, 1, 6, 8, 7, 3, 5, 4, 9 ]:
 Order := 54 > |
[ 5, 4, 2, 1, 9, 7, 6, 8, 3 ],
[ 7, 6, 4, 3, 5, 9, 2, 1, 8 ],
[ 3, 4, 6, 7, 8, 1, 2, 9, 5 ]
],
[ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 1, 2, 4, 5, 3, 8, 6, 7, 9 ],
\[ 2, 1, 6, 8, 7, 3, 5, 4, 9 ]:
 Order := 54 > |
[ 5, 4, 2, 1, 9, 7, 6, 8, 3 ],
[ 6, 8, 5, 4, 3, 9, 2, 1, 7 ],
[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]
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
