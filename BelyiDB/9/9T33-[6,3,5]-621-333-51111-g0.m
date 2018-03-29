s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T33-[6,3,5]-621-333-51111-g0";
s`BelyiDBFilename := "9T33-[6,3,5]-621-333-51111-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 6, 3, 5 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 5, 7, 9, 4, 6, 2, 8, 1, 3 ],
[ 9, 8, 1, 6, 4, 5, 2, 7, 3 ],
[ 2, 4, 1, 5, 3, 6, 7, 8, 9 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 5, 7, 9, 4, 6, 2, 8, 1, 3 ],
\[ 9, 8, 1, 6, 4, 5, 2, 7, 3 ],
\[ 2, 4, 1, 5, 3, 6, 7, 8, 9 ]:
 Order := 181440 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 5, 7, 9, 4, 6, 2, 8, 1, 3 ],
\[ 9, 8, 1, 6, 4, 5, 2, 7, 3 ],
\[ 2, 4, 1, 5, 3, 6, 7, 8, 9 ]:
 Order := 181440 >) |
[ PermutationGroup<9 |  
\[ 5, 7, 9, 4, 6, 2, 8, 1, 3 ],
\[ 9, 8, 1, 6, 4, 5, 2, 7, 3 ],
\[ 2, 4, 1, 5, 3, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 6, 1, 2, 3, 4, 5, 8, 7, 9 ],
[ 5, 7, 4, 9, 6, 1, 8, 2, 3 ],
[ 8, 9, 3, 1, 5, 6, 7, 2, 4 ]
],
[ PermutationGroup<9 |  
\[ 5, 7, 9, 4, 6, 2, 8, 1, 3 ],
\[ 9, 8, 1, 6, 4, 5, 2, 7, 3 ],
\[ 2, 4, 1, 5, 3, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 6, 1, 2, 3, 4, 5, 8, 7, 9 ],
[ 9, 7, 4, 5, 3, 1, 8, 2, 6 ],
[ 8, 5, 3, 4, 9, 6, 7, 2, 1 ]
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
[ 5, 7, 9, 4, 6, 2, 8, 1, 3 ],
[ 9, 8, 1, 6, 4, 5, 2, 7, 3 ],
[ 2, 4, 1, 5, 3, 6, 7, 8, 9 ]
],
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 8, 6, 9, 2, 5, 7, 1, 4, 3 ],
[ 5, 7, 4, 9, 8, 2, 6, 1, 3 ],
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
