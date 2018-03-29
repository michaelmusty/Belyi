s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T33-[9,3,3]-9-333-33111-g1";
s`BelyiDBFilename := "9T33-[9,3,3]-9-333-33111-g1.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 9, 3, 3 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 3;
s`BelyiDBPointedSize := 3;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 8, 5, 4, 2, 6, 7, 1, 9, 3 ],
[ 9, 7, 4, 5, 3, 2, 6, 1, 8 ],
[ 2, 3, 1, 5, 6, 4, 7, 8, 9 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 8, 5, 4, 2, 6, 7, 1, 9, 3 ],
\[ 9, 7, 4, 5, 3, 2, 6, 1, 8 ],
\[ 2, 3, 1, 5, 6, 4, 7, 8, 9 ]:
 Order := 181440 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 8, 5, 4, 2, 6, 7, 1, 9, 3 ],
\[ 9, 7, 4, 5, 3, 2, 6, 1, 8 ],
\[ 2, 3, 1, 5, 6, 4, 7, 8, 9 ]:
 Order := 181440 >) |
[ PermutationGroup<9 |  
\[ 8, 5, 4, 2, 6, 7, 1, 9, 3 ],
\[ 9, 7, 4, 5, 3, 2, 6, 1, 8 ],
\[ 2, 3, 1, 5, 6, 4, 7, 8, 9 ]:
 Order := 181440 > |
[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
[ 3, 9, 4, 1, 7, 5, 6, 2, 8 ],
[ 2, 4, 8, 1, 3, 6, 7, 5, 9 ]
],
[ PermutationGroup<9 |  
\[ 8, 5, 4, 2, 6, 7, 1, 9, 3 ],
\[ 9, 7, 4, 5, 3, 2, 6, 1, 8 ],
\[ 2, 3, 1, 5, 6, 4, 7, 8, 9 ]:
 Order := 181440 > |
[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
[ 2, 4, 6, 1, 3, 5, 9, 7, 8 ],
[ 7, 4, 1, 5, 2, 6, 3, 8, 9 ]
],
[ PermutationGroup<9 |  
\[ 8, 5, 4, 2, 6, 7, 1, 9, 3 ],
\[ 9, 7, 4, 5, 3, 2, 6, 1, 8 ],
\[ 2, 3, 1, 5, 6, 4, 7, 8, 9 ]:
 Order := 181440 > |
[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
[ 6, 8, 9, 3, 1, 5, 2, 7, 4 ],
[ 3, 5, 7, 4, 9, 6, 1, 8, 2 ]
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
[ 8, 5, 4, 2, 6, 7, 1, 9, 3 ],
[ 9, 7, 4, 5, 3, 2, 6, 1, 8 ],
[ 2, 3, 1, 5, 6, 4, 7, 8, 9 ]
],
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 4, 6, 1, 2, 9, 7, 8, 5, 3 ],
[ 9, 3, 4, 2, 1, 8, 6, 7, 5 ],
[ 2, 3, 1, 5, 6, 4, 7, 8, 9 ]
],
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 7, 9, 5, 3, 1, 8, 6, 2, 4 ],
[ 4, 5, 8, 7, 9, 3, 1, 6, 2 ],
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
