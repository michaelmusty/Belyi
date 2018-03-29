s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T43-[8,8,4]-8-8-44-g3";
s`BelyiDBFilename := "8T43-[8,8,4]-8-8-44-g3.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 8, 8, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 3;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 8, 7, 1 ],
\[ 3, 6, 2, 5, 1, 4, 7, 8 ],
\[ 6, 3, 2, 5, 4, 1, 8, 7 ]:
 Order := 336 > |
[ 5, 1, 2, 6, 8, 3, 4, 7 ],
[ 5, 8, 4, 2, 7, 3, 6, 1 ],
[ 4, 6, 7, 5, 8, 3, 2, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 5, 1, 2, 6, 8, 3, 4, 7 ],
\[ 5, 8, 4, 2, 7, 3, 6, 1 ],
\[ 4, 6, 7, 5, 8, 3, 2, 1 ]:
 Order := 336 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 5, 1, 2, 6, 8, 3, 4, 7 ],
\[ 5, 8, 4, 2, 7, 3, 6, 1 ],
\[ 4, 6, 7, 5, 8, 3, 2, 1 ]:
 Order := 336 >) |
[ PermutationGroup<8 |  
\[ 5, 1, 2, 6, 8, 3, 4, 7 ],
\[ 5, 8, 4, 2, 7, 3, 6, 1 ],
\[ 4, 6, 7, 5, 8, 3, 2, 1 ]:
 Order := 336 > |
[ 5, 1, 2, 6, 8, 3, 4, 7 ],
[ 8, 1, 5, 6, 2, 7, 3, 4 ],
[ 5, 7, 4, 6, 2, 8, 1, 3 ]
],
[ PermutationGroup<8 |  
\[ 5, 1, 2, 6, 8, 3, 4, 7 ],
\[ 5, 8, 4, 2, 7, 3, 6, 1 ],
\[ 4, 6, 7, 5, 8, 3, 2, 1 ]:
 Order := 336 > |
[ 5, 1, 2, 6, 8, 3, 4, 7 ],
[ 6, 4, 1, 3, 8, 5, 2, 7 ],
[ 7, 4, 1, 8, 3, 2, 5, 6 ]
],
[ PermutationGroup<8 |  
\[ 5, 1, 2, 6, 8, 3, 4, 7 ],
\[ 5, 8, 4, 2, 7, 3, 6, 1 ],
\[ 4, 6, 7, 5, 8, 3, 2, 1 ]:
 Order := 336 > |
[ 7, 8, 5, 2, 4, 1, 3, 6 ],
[ 8, 1, 5, 6, 2, 7, 3, 4 ],
[ 4, 8, 6, 3, 7, 1, 2, 5 ]
],
[ PermutationGroup<8 |  
\[ 5, 1, 2, 6, 8, 3, 4, 7 ],
\[ 5, 8, 4, 2, 7, 3, 6, 1 ],
\[ 4, 6, 7, 5, 8, 3, 2, 1 ]:
 Order := 336 > |
[ 7, 8, 5, 2, 4, 1, 3, 6 ],
[ 8, 3, 4, 1, 2, 5, 6, 7 ],
[ 7, 3, 8, 6, 2, 1, 4, 5 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 8, 7, 1 ],
\[ 3, 6, 2, 5, 1, 4, 7, 8 ],
\[ 6, 3, 2, 5, 4, 1, 8, 7 ]:
 Order := 336 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 8, 7, 1 ],
\[ 3, 6, 2, 5, 1, 4, 7, 8 ],
\[ 6, 3, 2, 5, 4, 1, 8, 7 ]:
 Order := 336 > |
[ 5, 1, 2, 6, 8, 3, 4, 7 ],
[ 5, 8, 4, 2, 7, 3, 6, 1 ],
[ 4, 6, 7, 5, 8, 3, 2, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 8, 7, 1 ],
\[ 3, 6, 2, 5, 1, 4, 7, 8 ],
\[ 6, 3, 2, 5, 4, 1, 8, 7 ]:
 Order := 336 > |
[ 5, 8, 1, 3, 2, 7, 4, 6 ],
[ 2, 6, 8, 3, 7, 5, 4, 1 ],
[ 4, 6, 7, 5, 8, 3, 2, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 8, 7, 1 ],
\[ 3, 6, 2, 5, 1, 4, 7, 8 ],
\[ 6, 3, 2, 5, 4, 1, 8, 7 ]:
 Order := 336 > |
[ 6, 4, 1, 3, 8, 5, 2, 7 ],
[ 5, 8, 1, 3, 2, 7, 4, 6 ],
[ 4, 6, 7, 5, 8, 3, 2, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 8, 7, 1 ],
\[ 3, 6, 2, 5, 1, 4, 7, 8 ],
\[ 6, 3, 2, 5, 4, 1, 8, 7 ]:
 Order := 336 > |
[ 6, 3, 5, 2, 8, 7, 4, 1 ],
[ 5, 6, 1, 8, 7, 4, 2, 3 ],
[ 4, 6, 7, 5, 8, 3, 2, 1 ]
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
