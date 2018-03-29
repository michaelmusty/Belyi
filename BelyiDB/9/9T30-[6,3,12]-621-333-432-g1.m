s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T30-[6,3,12]-621-333-432-g1";
s`BelyiDBFilename := "9T30-[6,3,12]-621-333-432-g1.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 6, 3, 12 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 1, 2, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 2, 1, 6, 7, 8, 3, 4, 5, 9 ]:
 Order := 648 > |
[ 3, 4, 9, 1, 2, 8, 7, 6, 5 ],
[ 3, 4, 6, 7, 8, 1, 2, 9, 5 ],
[ 2, 9, 6, 7, 8, 5, 4, 3, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 3, 4, 9, 1, 2, 8, 7, 6, 5 ],
\[ 3, 4, 6, 7, 8, 1, 2, 9, 5 ],
\[ 2, 9, 6, 7, 8, 5, 4, 3, 1 ]:
 Order := 648 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 3, 4, 9, 1, 2, 8, 7, 6, 5 ],
\[ 3, 4, 6, 7, 8, 1, 2, 9, 5 ],
\[ 2, 9, 6, 7, 8, 5, 4, 3, 1 ]:
 Order := 648 >) |
[ PermutationGroup<9 |  
\[ 3, 4, 9, 1, 2, 8, 7, 6, 5 ],
\[ 3, 4, 6, 7, 8, 1, 2, 9, 5 ],
\[ 2, 9, 6, 7, 8, 5, 4, 3, 1 ]:
 Order := 648 > |
[ 4, 5, 1, 2, 9, 8, 7, 6, 3 ],
[ 4, 5, 8, 7, 6, 2, 1, 9, 3 ],
[ 9, 1, 8, 7, 6, 3, 4, 5, 2 ]
],
[ PermutationGroup<9 |  
\[ 3, 4, 9, 1, 2, 8, 7, 6, 5 ],
\[ 3, 4, 6, 7, 8, 1, 2, 9, 5 ],
\[ 2, 9, 6, 7, 8, 5, 4, 3, 1 ]:
 Order := 648 > |
[ 4, 5, 1, 2, 9, 8, 7, 6, 3 ],
[ 5, 3, 8, 6, 7, 9, 1, 2, 4 ],
[ 2, 9, 6, 7, 8, 3, 5, 4, 1 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 1, 2, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 2, 1, 6, 7, 8, 3, 4, 5, 9 ]:
 Order := 648 >) |
[ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 1, 2, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 2, 1, 6, 7, 8, 3, 4, 5, 9 ]:
 Order := 648 > |
[ 3, 4, 9, 1, 2, 8, 7, 6, 5 ],
[ 3, 4, 6, 7, 8, 1, 2, 9, 5 ],
[ 2, 9, 6, 7, 8, 5, 4, 3, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 1, 2, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 2, 1, 6, 7, 8, 3, 4, 5, 9 ]:
 Order := 648 > |
[ 5, 3, 9, 1, 2, 6, 8, 7, 4 ],
[ 3, 4, 6, 7, 8, 1, 2, 9, 5 ],
[ 2, 9, 7, 8, 6, 3, 5, 4, 1 ]
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
