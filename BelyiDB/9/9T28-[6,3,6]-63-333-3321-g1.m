s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T28-[6,3,6]-63-333-3321-g1";
s`BelyiDBFilename := "9T28-[6,3,6]-63-333-3321-g1.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 6, 3, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 648 > |
[ 3, 4, 6, 8, 7, 2, 9, 1, 5 ],
[ 6, 8, 9, 1, 2, 4, 3, 5, 7 ],
[ 2, 1, 4, 5, 3, 7, 8, 6, 9 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 3, 4, 6, 8, 7, 2, 9, 1, 5 ],
\[ 6, 8, 9, 1, 2, 4, 3, 5, 7 ],
\[ 2, 1, 4, 5, 3, 7, 8, 6, 9 ]:
 Order := 648 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 3, 4, 6, 8, 7, 2, 9, 1, 5 ],
\[ 6, 8, 9, 1, 2, 4, 3, 5, 7 ],
\[ 2, 1, 4, 5, 3, 7, 8, 6, 9 ]:
 Order := 648 >) |
[ PermutationGroup<9 |  
\[ 3, 4, 6, 8, 7, 2, 9, 1, 5 ],
\[ 6, 8, 9, 1, 2, 4, 3, 5, 7 ],
\[ 2, 1, 4, 5, 3, 7, 8, 6, 9 ]:
 Order := 648 > |
[ 3, 4, 6, 8, 7, 2, 9, 1, 5 ],
[ 6, 8, 2, 9, 1, 5, 4, 3, 7 ],
[ 2, 1, 5, 3, 4, 8, 6, 7, 9 ]
],
[ PermutationGroup<9 |  
\[ 3, 4, 6, 8, 7, 2, 9, 1, 5 ],
\[ 6, 8, 9, 1, 2, 4, 3, 5, 7 ],
\[ 2, 1, 4, 5, 3, 7, 8, 6, 9 ]:
 Order := 648 > |
[ 3, 4, 6, 8, 7, 2, 9, 1, 5 ],
[ 6, 7, 2, 9, 1, 5, 3, 4, 8 ],
[ 9, 1, 5, 3, 4, 7, 6, 8, 2 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 648 >) |
[ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 648 > |
[ 3, 4, 6, 8, 7, 2, 9, 1, 5 ],
[ 6, 8, 9, 1, 2, 4, 3, 5, 7 ],
[ 2, 1, 4, 5, 3, 7, 8, 6, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 648 > |
[ 3, 5, 6, 7, 8, 2, 9, 1, 4 ],
[ 8, 7, 2, 1, 9, 5, 3, 4, 6 ],
[ 1, 9, 4, 5, 3, 7, 8, 6, 2 ]
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
