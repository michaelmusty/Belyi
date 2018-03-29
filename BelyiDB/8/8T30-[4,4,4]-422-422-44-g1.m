s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T30-[4,4,4]-422-422-44-g1";
s`BelyiDBFilename := "8T30-[4,4,4]-422-422-44-g1.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 4, 4, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 1, 6, 7, 4, 5, 2, 3, 8 ],
\[ 3, 2, 1, 8, 7, 6, 5, 4 ],
\[ 2, 3, 8, 5, 6, 7, 4, 1 ]:
 Order := 64 > |
[ 7, 6, 1, 8, 3, 2, 5, 4 ],
[ 4, 3, 2, 5, 8, 7, 6, 1 ],
[ 2, 7, 4, 5, 6, 3, 8, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |  
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 2 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |  
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 2 >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 7, 6, 1, 8, 3, 2, 5, 4 ],
\[ 4, 3, 2, 5, 8, 7, 6, 1 ],
\[ 2, 7, 4, 5, 6, 3, 8, 1 ]:
 Order := 64 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 7, 6, 1, 8, 3, 2, 5, 4 ],
\[ 4, 3, 2, 5, 8, 7, 6, 1 ],
\[ 2, 7, 4, 5, 6, 3, 8, 1 ]:
 Order := 64 >) |
[ PermutationGroup<8 |  
\[ 7, 6, 1, 8, 3, 2, 5, 4 ],
\[ 4, 3, 2, 5, 8, 7, 6, 1 ],
\[ 2, 7, 4, 5, 6, 3, 8, 1 ]:
 Order := 64 > |
[ 7, 6, 1, 8, 3, 2, 5, 4 ],
[ 4, 3, 2, 5, 8, 7, 6, 1 ],
[ 2, 7, 4, 5, 6, 3, 8, 1 ]
],
[ PermutationGroup<8 |  
\[ 7, 6, 1, 8, 3, 2, 5, 4 ],
\[ 4, 3, 2, 5, 8, 7, 6, 1 ],
\[ 2, 7, 4, 5, 6, 3, 8, 1 ]:
 Order := 64 > |
[ 4, 3, 2, 5, 8, 7, 6, 1 ],
[ 7, 6, 1, 8, 3, 2, 5, 4 ],
[ 4, 5, 6, 3, 8, 1, 2, 7 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 1, 6, 7, 4, 5, 2, 3, 8 ],
\[ 3, 2, 1, 8, 7, 6, 5, 4 ],
\[ 2, 3, 8, 5, 6, 7, 4, 1 ]:
 Order := 64 >) |
[ PermutationGroup<8 |  
\[ 1, 6, 7, 4, 5, 2, 3, 8 ],
\[ 3, 2, 1, 8, 7, 6, 5, 4 ],
\[ 2, 3, 8, 5, 6, 7, 4, 1 ]:
 Order := 64 > |
[ 7, 6, 1, 8, 3, 2, 5, 4 ],
[ 4, 3, 2, 5, 8, 7, 6, 1 ],
[ 2, 7, 4, 5, 6, 3, 8, 1 ]
],
[ PermutationGroup<8 |  
\[ 1, 6, 7, 4, 5, 2, 3, 8 ],
\[ 3, 2, 1, 8, 7, 6, 5, 4 ],
\[ 2, 3, 8, 5, 6, 7, 4, 1 ]:
 Order := 64 > |
[ 8, 3, 2, 1, 4, 7, 6, 5 ],
[ 3, 6, 5, 8, 7, 2, 1, 4 ],
[ 8, 1, 6, 3, 4, 5, 2, 7 ]
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
