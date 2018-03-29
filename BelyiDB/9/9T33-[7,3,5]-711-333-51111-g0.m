s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T33-[7,3,5]-711-333-51111-g0";
s`BelyiDBFilename := "9T33-[7,3,5]-711-333-51111-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 7, 3, 5 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 8, 6, 3, 4, 2, 7, 1, 9, 5 ],
[ 9, 7, 5, 3, 4, 2, 6, 1, 8 ],
[ 2, 3, 4, 5, 1, 6, 7, 8, 9 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 8, 6, 3, 4, 2, 7, 1, 9, 5 ],
\[ 9, 7, 5, 3, 4, 2, 6, 1, 8 ],
\[ 2, 3, 4, 5, 1, 6, 7, 8, 9 ]:
 Order := 181440 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 8, 6, 3, 4, 2, 7, 1, 9, 5 ],
\[ 9, 7, 5, 3, 4, 2, 6, 1, 8 ],
\[ 2, 3, 4, 5, 1, 6, 7, 8, 9 ]:
 Order := 181440 >) |
[ PermutationGroup<9 |  
\[ 8, 6, 3, 4, 2, 7, 1, 9, 5 ],
\[ 9, 7, 5, 3, 4, 2, 6, 1, 8 ],
\[ 2, 3, 4, 5, 1, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 7, 1, 2, 3, 4, 5, 6, 8, 9 ],
[ 9, 3, 4, 2, 6, 7, 5, 1, 8 ],
[ 4, 2, 3, 7, 5, 6, 8, 9, 1 ]
],
[ PermutationGroup<9 |  
\[ 8, 6, 3, 4, 2, 7, 1, 9, 5 ],
\[ 9, 7, 5, 3, 4, 2, 6, 1, 8 ],
\[ 2, 3, 4, 5, 1, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 7, 1, 2, 3, 4, 5, 6, 8, 9 ],
[ 2, 8, 4, 5, 3, 7, 9, 1, 6 ],
[ 1, 5, 3, 4, 9, 6, 8, 2, 7 ]
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
[ 8, 6, 3, 4, 2, 7, 1, 9, 5 ],
[ 9, 7, 5, 3, 4, 2, 6, 1, 8 ],
[ 2, 3, 4, 5, 1, 6, 7, 8, 9 ]
],
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 9, 7, 3, 6, 5, 2, 8, 1, 4 ],
[ 5, 8, 6, 3, 9, 4, 2, 7, 1 ],
[ 2, 3, 4, 5, 1, 6, 7, 8, 9 ]
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
